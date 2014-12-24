/*
 * ring.c
 *
 *  Created on: 6.12.2014
 *      Author: marshynk
 */

#include "ring.h"

#include <memory.h>
#include <stdlib.h>
#include <pthread.h>

#include <stdio.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>

#include <sys/ioctl.h>
#include <sys/mman.h>
#include <net/if.h>
#include <linux/if_ether.h>
#include <linux/if_packet.h>
#include <netinet/in.h>
#include <poll.h>
#include <errno.h>

/* After my latest tests I found that: page count as bigger as better for slow path,
 * whereas more elem count is better for fast path. E.g: in case producer is faster than consumer,
 * it is better to have more elements in the page as the recent accessed page is cached thus not interfere with
 * lock-free queue. On the other hand, slow or bouncing consumer would miss a packet if page queue is short.
 *
 * These numbers were predefined for fast producer and slow consumer.
 */

#define RING_PAGE_COUNT          ( 1024 * 8 )
#define RING_ELEM_COUNT          ( 8 )

#define RING_PAYLOAD_SIZE        1600

/*
 * It is mandatory to have atleast RingPtr to be 8 bytes aligned
 * in structure
 * */
#pragma pack( push, 8 )

typedef struct RingPtr
{
   struct RingPage* _ptr;
   unsigned int _counter;
}
RingPtr;

typedef struct RingElem
{
   uint8_t _payload[ RING_PAYLOAD_SIZE ];
   uint16_t _len;
}
RingElem;

typedef struct RingData
{
   RingElem _elem[ RING_ELEM_COUNT ];
   uint16_t _count;
}
RingData;

typedef struct RingPage
{
   struct RingPtr volatile _next;

   RingData _prod_data;
   RingData* _cons_data;

   /*
    * For debuging purposes
    * */
   int _num;
}
RingPage;

/*
 * Must be 8 bytes aligned in structure
 * */
typedef struct RingList
{
   __attribute__(( aligned( 8 ) )) struct RingPtr volatile _head;
   __attribute__(( aligned( 8 ) )) struct RingPtr volatile _tail;
}
RingList;

typedef struct Ring
{
   /*
    * Signaling. Not necessary if consumer/producer are
    * running on dedicated core. Hovewer, signalling allows
    * to analyze core utilization
    * */
   pthread_mutex_t _prod_mutex;
   pthread_cond_t _prod_cond;

   pthread_mutex_t _cons_mutex;
   pthread_cond_t _cons_cond;

   int _prod_wanted;
   int _cons_wanted;

   int _prod_q_size;
   int _cons_q_size;

   /*
    * Must be 8 bytes aligned for fast DCAS operation. Missalignmet
    * causes -30% of performance
    * */
   __attribute__(( aligned( 8 ) )) RingList _reader;
   __attribute__(( aligned( 8 ) )) RingList _writer;

   /*
    * Cached page. producer uses it to try to fill all elements
    * without page get/put operation. Consumer may take the cahe
    * in case if main consumer's queue is empty. Produced always puts
    * the cache.
    * */
   __attribute__(( aligned( 4 ) )) RingPage* volatile _cache;
}
Ring;

#pragma pack( pop )

/*
 * Compiler usually 4 byte aligns. Added as prevention
 * */
static __attribute__(( aligned( 8 ) )) Ring g_RingRx;
static __attribute__(( aligned( 8 ) )) Ring g_RingTx;

static pthread_t g_RxThreadId;
static pthread_t g_ProcThreadId;
static pthread_t g_TxThreadId;

/*
 * Stats for debugging purposes
 * */
static int g_RxCount = 0;
static int g_TxCount = 0;
static int g_ProcCount = 0;
static int g_PutCount = 0;

static int g_PutLoopCount = 0;
static int g_GetLoopCount = 0;

static int g_PutGetFailCount = 0;
static int g_TxGetFailCount = 0;
static int g_ProcGetFailCount = 0;
static int g_RxGetFailCount = 0;

static int g_SigPrCount = 0;
static int g_SigCsCount = 0;

static int g_PrintGuard = 0;

void ring_debug_print();

/*
 * Dequeues page from FIFO
 * */
static __inline RingPage* ring_get_page( Ring* aRing, RingList* aQueue )
{
   /*
    * Soft memory bariers for DCAS
    * */
   __asm__ __volatile__ ( "" : : : "memory" );
   __sync_synchronize();

   /*
    * Usually compiler aligned. Prevention.
    * */
   __attribute__(( aligned( 8 ) )) RingPtr theHead;
   __attribute__(( aligned( 8 ) )) RingPtr theTail;
   __attribute__(( aligned( 8 ) )) RingPtr theNext;

   __attribute__(( aligned( 8 ) )) RingPtr ret;

   while( 1 )
   {
      theHead = aQueue->_head;
      theTail = aQueue->_tail;
      theNext = theHead._ptr->_next;

      /*
       * Consistency check for debugging. Do not remove comments
       * */
      //if( theHead._ptr == aQueue->_head._ptr &&
      //      theHead._counter == aQueue->_head._counter )
      {
         if( theHead._ptr == theTail._ptr )
         {
            if( !theNext._ptr )
            {
               ret = theNext;
               break;
            }

            theNext._counter = theTail._counter + 1;

            *(( unsigned long long int* )&ret) = ( unsigned long long int )__sync_val_compare_and_swap( ( volatile unsigned long long int* )&aQueue->_tail,
                                                *( unsigned long long int* )&theTail, *( unsigned long long int* )&theNext );
         }
         else
         {
            RingData* theData = &theNext._ptr->_prod_data;

            theNext._counter = theHead._counter + 1;

            *(( unsigned long long int* )&ret) = ( unsigned long long int )__sync_val_compare_and_swap( ( volatile unsigned long long int* )&aQueue->_head,
                                                *( unsigned long long int* )&theHead, *( unsigned long long int* )&theNext );


            if( ret._ptr == theHead._ptr &&
                  ret._counter == theHead._counter )
            {
               ret._ptr->_cons_data = theData;
               break;
            }
         }
      }

      ++g_GetLoopCount;
   }

   return ret._ptr;
}

/*
 * Enqueues page to FIFO
 * */
static __inline void ring_put_page( Ring* aRing, RingPage* aPage, RingList* aQueue )
{
   /*
    * Soft memory bariers for DCAS
    * */
   __asm__ __volatile__ ( "" : : : "memory" );
   __sync_synchronize();

   /*
    * Usually compiler aligned. Prevention.
    * */
   __attribute__(( aligned( 8 ) )) RingPtr theTail;
   __attribute__(( aligned( 8 ) )) RingPtr theNext;
   __attribute__(( aligned( 8 ) )) RingPtr ret;

   aPage->_next._ptr = 0;
   aPage->_next._counter = 0;

   __attribute__(( aligned( 8 ) )) RingPtr thePage;

   thePage._ptr = aPage;
   thePage._counter = 0;

   while( 1 )
   {
      theTail = aQueue->_tail;
      theNext = theTail._ptr->_next;

      /*
       * Consistency check for debugging. Do not remove comments
       * */
      //if( theTail._ptr == aQueue->_tail._ptr &&
      //      theTail._counter == aQueue->_tail._counter )
      {
         if( !theNext._ptr )
         {
            thePage._counter = theNext._counter + 1;

            *(( unsigned long long int* )&ret) = ( unsigned long long int )__sync_val_compare_and_swap( ( volatile unsigned long long int* )&theTail._ptr->_next,
                                                *( unsigned long long int* )&theNext, *( unsigned long long int* )&thePage );

            if( ret._ptr == theNext._ptr &&
                  ret._counter == theNext._counter )
            {
               break;
            }
         }
         else
         {
            theNext._counter = theTail._counter + 1;

            *(( unsigned long long int* )&ret) = ( unsigned long long int )__sync_val_compare_and_swap( ( volatile unsigned long long int* )&aQueue->_tail,
                                                *( unsigned long long int* )&theTail, *( unsigned long long int* )&theNext );
         }
      }

      ++g_PutLoopCount;
   }

   thePage._counter = theTail._counter + 1;

   *(( unsigned long long int* )&ret) = ( unsigned long long int )__sync_val_compare_and_swap( ( volatile unsigned long long int* )&aQueue->_tail,
                                       *( unsigned long long int* )&theTail, *( unsigned long long int* )&thePage );
}

static __inline RingPage* ring_get_write_page( Ring* aRing )
{
   RingPage* ret = ring_get_page( aRing, &aRing->_writer );

   if( ret )
   {
      __sync_fetch_and_sub( &aRing->_prod_q_size, 1 );
   }

   return ret;
}

static __inline RingPage* ring_get_read_page( Ring* aRing )
{
   RingPage* ret = ring_get_page( aRing, &aRing->_reader );

   if( ret )
   {
      __sync_fetch_and_sub( &aRing->_cons_q_size, 1 );
   }

   return ret;
}

static __inline void ring_put_write_page( Ring* aRing, RingPage* anElem )
{
   ring_put_page( aRing, anElem, &aRing->_reader );

   __sync_fetch_and_add( &aRing->_cons_q_size, 1 );
}

static __inline void ring_put_read_page( Ring* aRing, RingPage* anElem )
{
   ring_put_page( aRing, anElem, &aRing->_writer );

   /*
    * Signal producer no later than half of a ring was processed.
    * It is possible to do it erlier but in case of fast producer
    * the core will be flooded with syscalls
    * */
   if( __sync_add_and_fetch( &aRing->_prod_q_size, 1 ) > ( RING_PAGE_COUNT / 2 ) )
   {
      pthread_mutex_lock( &aRing->_prod_mutex );

      if( aRing->_prod_wanted > 0 )
      {
         pthread_cond_signal( &aRing->_prod_cond );

         --aRing->_prod_wanted;

         ++g_SigPrCount;
      }
      else if( !aRing->_prod_wanted )
      {
         aRing->_prod_wanted = -1;
      }

      pthread_mutex_unlock( &aRing->_prod_mutex );
   }
}

/*
 * Cache routines
 * */
static __inline RingPage* ring_try_get_cache( Ring* aRing )
{
   RingPage* ret = 0;

   __attribute__(( aligned( 4 ) )) RingPage* theCache = aRing->_cache;

   ret = __sync_val_compare_and_swap( &aRing->_cache, theCache, 0 );

   if( theCache != ret )
   {
      ret = 0;
   }
   else if( ret )
   {
      ret->_cons_data = &ret->_prod_data;
   }

   return ret;
}

static __inline uint8_t ring_try_put_cache( Ring* aRing, RingPage* aPage )
{
   RingPage* theCache = __sync_val_compare_and_swap( &aRing->_cache, 0, aPage );

   return !theCache;
}

/*
 * Signaling routines
 *
 * Mutexes causes context switch which would slow the system down,
 * however, in this algorithm, such condition is very rare and might
 * only happen if one of the sides slover than other.
 * */
static __inline void ring_wait_consumer_signal( Ring* aRing )
{
   pthread_mutex_lock( &aRing->_prod_mutex );

   ++aRing->_prod_wanted;

   if( aRing->_prod_wanted > 0 )
   {
      pthread_cond_wait( &aRing->_prod_cond, &aRing->_prod_mutex );
   }

   pthread_mutex_unlock( &aRing->_prod_mutex );
}

static __inline void ring_wait_producer_signal( Ring* aRing )
{
   pthread_mutex_lock( &aRing->_cons_mutex );

   ++aRing->_cons_wanted;

   if( aRing->_cons_wanted > 0 )
   {
      pthread_cond_wait( &aRing->_cons_cond, &aRing->_cons_mutex );
   }

   pthread_mutex_unlock( &aRing->_cons_mutex );
}

static __inline void ring_signal_consumer( Ring* aRing )
{
   int consSig = aRing->_cons_q_size;

   if( __sync_val_compare_and_swap( &aRing->_cons_q_size, consSig, consSig ) <= 1 )
   {
      pthread_mutex_lock( &aRing->_cons_mutex );

      if( aRing->_cons_wanted > 0 )
      {
         pthread_cond_signal( &aRing->_cons_cond );

         --aRing->_cons_wanted;

         ++g_SigCsCount;
      }
      else if( !aRing->_cons_wanted )
      {
         aRing->_cons_wanted = -1;
      }

      pthread_mutex_unlock( &aRing->_cons_mutex );
   }
}

/*
 * Producer/Consumer routines
 * */
static void* ring_rx_thread( void* anArg )
{
   int theSock = ( int )anArg;

   RingPage* I_page = 0;

   do
   {
      do
      {
         I_page = ring_try_get_cache( &g_RingRx );

         if( !I_page )
         {
            I_page = ring_get_write_page( &g_RingRx );
         }

         if( !I_page )
         {
            ++g_RxGetFailCount;

            ring_wait_consumer_signal( &g_RingRx );

            continue;
         }
      }
      while( !I_page );

      int theLen = 0;
      int theMode = 0;

      do
      {
         theMode = ( I_page->_prod_data._count ? MSG_DONTWAIT : 0 );

         if( ( theLen = recv( theSock, I_page->_prod_data._elem[ I_page->_prod_data._count ]._payload, RING_PAYLOAD_SIZE, theMode ) ) > 0 )
         {
            I_page->_prod_data._elem[ I_page->_prod_data._count ]._len = theLen;
         }
         else
         {
            I_page->_prod_data._elem[ I_page->_prod_data._count ]._len = 0;
         }

         ++I_page->_prod_data._count;
      }
      while( theLen > 0 && ( I_page->_prod_data._count < RING_ELEM_COUNT ) );

      if( ( I_page->_prod_data._count == RING_ELEM_COUNT ) || !ring_try_put_cache( &g_RingRx, I_page ) )
      {
         ring_put_write_page( &g_RingRx, I_page );
      }

      ring_signal_consumer( &g_RingRx );

      ++g_RxCount;
   }
   while( I_page );

   return 0;
}

void ring_tx( uint8_t* aData, uint16_t aSize )
{
   if( !aSize )
   {
      return;
   }

   RingPage* I_page = 0;

   do
   {
      I_page = ring_try_get_cache( &g_RingTx );

      if( !I_page )
      {
         I_page = ring_get_write_page( &g_RingTx );
      }

      if( !I_page )
      {
         ++g_PutGetFailCount;

         ring_wait_consumer_signal( &g_RingTx );

         continue;
      }
   }
   while( !I_page );

   memcpy( I_page->_prod_data._elem[ I_page->_prod_data._count ]._payload, aData, aSize );

   I_page->_prod_data._elem[ I_page->_prod_data._count ]._len = aSize;

   ++I_page->_prod_data._count;

   if( I_page->_prod_data._count == RING_ELEM_COUNT || !ring_try_put_cache( &g_RingTx, I_page ) )
   {
      ring_put_write_page( &g_RingTx, I_page );
   }

   ring_signal_consumer( &g_RingTx );

   ++g_PutCount;
}

static void* ring_proc_thread( void* anArg )
{
   ProcessingHandler theHandler = ( ProcessingHandler )anArg;

   RingPage* I_page = 0;

   do
   {
      do
      {
         I_page = ring_get_read_page( &g_RingRx );

         if( !I_page )
         {
            I_page = ring_try_get_cache( &g_RingRx );
         }

         if( !I_page )
         {
            ++g_ProcGetFailCount;

            ring_wait_producer_signal( &g_RingRx );

            continue;
         }
      }
      while( !I_page );

      if( theHandler )
      {
         int i;
         for( i = 0; i < I_page->_cons_data->_count; ++i )
         {
            theHandler( I_page->_cons_data->_elem[ i ]._payload, I_page->_cons_data->_elem[ i ]._len );
            I_page->_cons_data->_elem[ i ]._len = 0;

            ++g_ProcCount;
         }
      }

      I_page->_cons_data->_count = 0;

      ring_put_read_page( &g_RingRx, I_page );
   }
   while( I_page );

   return 0;
}

static void* ring_tx_thread( void* anArg )
{
   int theSock = ( int )anArg;

   RingPage* I_page = 0;

   do
   {
      do
      {
         I_page = ring_get_read_page( &g_RingTx );

         if( !I_page )
         {
            I_page = ring_try_get_cache( &g_RingTx );
         }

         if( !I_page )
         {
            ++g_TxGetFailCount;

            ring_wait_producer_signal( &g_RingTx );

            continue;
         }
      }
      while( !I_page );

      int i;
      for( i = 0; i < I_page->_cons_data->_count; ++i )
      {
         if( send( theSock, I_page->_cons_data->_elem[ i ]._payload, I_page->_cons_data->_elem[ i ]._len, 0 ) == I_page->_cons_data->_elem[ i ]._len )
         {
            ++g_TxCount;
         }
         else
         {
            fprintf( stdout, "ring_tx_thread: error %d\n", errno );
         }

         I_page->_cons_data->_elem[ i ]._len = 0;
      }

      I_page->_cons_data->_count = 0;

      ring_put_read_page( &g_RingTx, I_page );
   }
   while( I_page );

   return 0;
}

static void ring_create( Ring* aRing )
{
   pthread_mutex_t theMutex = PTHREAD_MUTEX_INITIALIZER;
   pthread_cond_t theCond = PTHREAD_COND_INITIALIZER;

   aRing->_prod_mutex = theMutex;
   aRing->_prod_cond = theCond;

   aRing->_cons_mutex = theMutex;
   aRing->_cons_cond = theCond;

   aRing->_writer._head._ptr = ( RingPage* )calloc( 1, sizeof( RingPage ) );
   aRing->_writer._head._counter = 0;
   aRing->_writer._head._ptr->_num = 0;

   RingPtr thePrev = aRing->_writer._head;

   int I_elem;
   for( I_elem = 1; I_elem < RING_PAGE_COUNT + 1; ++I_elem )
   {
      thePrev._ptr->_next._ptr = ( RingPage* )calloc( 1, sizeof( RingPage ) );
      thePrev._ptr->_next._counter = 0;
      thePrev._ptr->_next._ptr->_num = I_elem;

      thePrev = thePrev._ptr->_next;
   }

   aRing->_writer._tail = thePrev;
   aRing->_writer._tail._ptr->_num = I_elem;

   ++I_elem;

   aRing->_reader._head._ptr = ( RingPage* )calloc( 1, sizeof( RingPage ) );
   aRing->_reader._head._counter = 0;
   aRing->_reader._head._ptr->_num = I_elem;

   aRing->_reader._tail = aRing->_reader._head;
}

int ring_init( int aSocket, ProcessingHandler aHandler )
{
   int ret = 0;

   int sockBufSize = 1024 * 256;

   if( setsockopt( aSocket, SOL_SOCKET, SO_RCVBUF, &sockBufSize, sizeof( sockBufSize ) ) != 0 )
   {
      perror( "setsockopt SO_RCVBUF" );
      close( aSocket );
      return -1;
   }

   if( setsockopt( aSocket, SOL_SOCKET, SO_SNDBUF, &sockBufSize, sizeof( sockBufSize ) ) != 0 )
   {
      perror( "setsockopt SO_SNDBUF" );
      close( aSocket );
      return -1;
   }

   ring_create( &g_RingRx );
   ring_create( &g_RingTx );

   g_RingTx._prod_q_size = RING_PAGE_COUNT;
   g_RingRx._prod_q_size = RING_PAGE_COUNT;

   pthread_attr_t theRxAttr;
   pthread_attr_t theTxAttr;

   struct sched_param theRxShed;
   memset( &theRxShed, 0, sizeof( theRxShed ) );

   struct sched_param theTxShed;
   memset( &theTxShed, 0, sizeof( theTxShed ) );

   pthread_attr_init( &theRxAttr );
   pthread_attr_init( &theTxAttr );

   pthread_attr_setschedpolicy( &theRxAttr, SCHED_RR );
   pthread_attr_setschedpolicy( &theTxAttr, SCHED_RR );

   theRxShed.sched_priority=20;
   pthread_attr_setschedparam( &theRxAttr, &theRxShed );

   theTxShed.sched_priority=20;
   pthread_attr_setschedparam( &theTxAttr, &theTxShed );

   pthread_create( &g_RxThreadId, 0, ring_rx_thread, ( void* )aSocket );
   pthread_create( &g_ProcThreadId, 0, ring_proc_thread, aHandler );
   pthread_create( &g_TxThreadId, &theTxAttr, ring_tx_thread, ( void* )aSocket );

   return ret;
}

void ring_uninit()
{

}

void ring_debug_print()
{
   if( !( g_PrintGuard++ % 300000 ) )
   {
      printf( "put lc: %d, get lc: %d, pgf: %d, tgf: %d, prgf: %d, rgf: %d\n",
              g_PutLoopCount, g_GetLoopCount, g_PutGetFailCount, g_TxGetFailCount, g_ProcGetFailCount, g_RxGetFailCount );

      printf( "tx: %d, rx: %d, put: %d, proc: %d\n", g_TxCount, g_RxCount, g_PutCount, g_ProcCount );

      printf( "ps: %d, cs: %d, s_pr: %d, s_cs: %d\n", g_RingTx._prod_q_size, g_RingTx._cons_q_size, g_SigPrCount, g_SigCsCount );

      g_PutLoopCount = 0;
      g_GetLoopCount = 0;
      g_PutGetFailCount = 0;
      g_TxGetFailCount = 0;
      g_ProcGetFailCount = 0;
      g_RxGetFailCount = 0;

      g_RxCount = 0;
      g_TxCount = 0;
      g_ProcCount = 0;
      g_PutCount = 0;

      g_SigPrCount = 0;
      g_SigCsCount = 0;

   }
}
