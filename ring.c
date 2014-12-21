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

#define RING_ELEMENT_COUNT       ( 1024 * 4 )
#define RING_PAYLOAD_SIZE        2048

#pragma pack( push, 8 )

typedef struct RingPtr
{
   struct RingElem* _ptr;
   unsigned int _counter;
}
RingPtr;

typedef struct RingElem
{
   struct RingPtr volatile _next;

   uint8_t _payload[ 16 ][ RING_PAYLOAD_SIZE ];
   uint16_t _len[ 16 ];

   uint16_t _count;

   int _num;
}
RingElem;

typedef struct RingList
{
   struct RingPtr volatile _head;
   struct RingPtr volatile _tail;

   pthread_spinlock_t _lock;
}
RingList;

#pragma pack( pop )

typedef struct Ring
{
   pthread_mutex_t _mutex;
   pthread_cond_t _cond;

   uint8_t _wanted;

   RingList _reader;
   RingList _writer;

   uint32_t _aba_counter;
}
Ring;

Ring g_RingRx;
Ring g_RingTx;

static pthread_t g_RxThreadId;
static pthread_t g_ProcThreadId;
static pthread_t g_TxThreadId;

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

static int g_PrintGuard = 0;

static void ring_debug_print();

static RingElem* ring_get_elem( Ring* aRing, RingList* aQueue )
{
   __asm__ __volatile__ ( "" : : : "memory" );
   __sync_synchronize();

   RingPtr theHead;
   RingPtr theTail;
   RingPtr theNext;

   RingPtr ret;

   while( 1 )
   {
      theHead = aQueue->_head;
      theTail = aQueue->_tail;
      theNext = theHead._ptr->_next;

      if( theHead._ptr == aQueue->_head._ptr &&
            theHead._counter == aQueue->_head._counter )
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
            theNext._counter = theHead._counter + 1;

            *(( unsigned long long int* )&ret) = ( unsigned long long int )__sync_val_compare_and_swap( ( volatile unsigned long long int* )&aQueue->_head,
                                                *( unsigned long long int* )&theHead, *( unsigned long long int* )&theNext );

            if( ret._ptr == theHead._ptr &&
                  ret._counter == theHead._counter )
            {
               break;
            }
         }
      }

      ++g_GetLoopCount;
   }

   return ret._ptr;
}

static void ring_put_elem( Ring* aRing, RingElem* anElem, RingList* aQueue )
{
   __asm__ __volatile__ ( "" : : : "memory" );
   __sync_synchronize();

   RingPtr theTail;
   RingPtr theNext;

   RingPtr ret;

   anElem->_next._ptr = 0;

   RingPtr theElem;
   theElem._ptr = anElem;
   theElem._counter = 0;

   while( 1 )
   {
      theTail = aQueue->_tail;
      theNext = theTail._ptr->_next;

      if( theTail._ptr == aQueue->_tail._ptr &&
            theTail._counter == aQueue->_tail._counter )
      {
         if( !theNext._ptr )
         {
            theElem._counter = theNext._counter + 1;

            *(( unsigned long long int* )&ret) = ( unsigned long long int )__sync_val_compare_and_swap( ( volatile unsigned long long int* )&theTail._ptr->_next,
                                                *( unsigned long long int* )&theNext, *( unsigned long long int* )&theElem );

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

   theElem._counter = theTail._counter + 1;

   *(( unsigned long long int* )&ret) = ( unsigned long long int )__sync_val_compare_and_swap( ( volatile unsigned long long int* )&aQueue->_tail,
                                       *( unsigned long long int* )&theTail, *( unsigned long long int* )&theElem );
}

static RingElem* ring_get_write_elem( Ring* aRing )
{
   return ring_get_elem( aRing, &aRing->_writer );
}

static RingElem* ring_get_read_elem( Ring* aRing )
{
   return ring_get_elem( aRing, &aRing->_reader );
}

static void ring_put_write_elem( Ring* aRing, RingElem* anElem )
{
   ring_put_elem( aRing, anElem, &aRing->_reader );
}

static void ring_put_read_elem( Ring* aRing, RingElem* anElem )
{
   ring_put_elem( aRing, anElem, &aRing->_writer );
}

static RingElem* g_rx_elem = 0;

static void* ring_rx_thread( void* anArg )
{
   int theSock = ( int )anArg;

   RingElem* I_elem = 0;

   do
   {
      while( 1 )
      {
         I_elem = __sync_val_compare_and_swap( &g_rx_elem, g_rx_elem, 0 );

         if( !I_elem )
         {
            I_elem = ring_get_write_elem( &g_RingRx );
         }

         if( !I_elem )
         {
            ++g_RxGetFailCount;

            pthread_mutex_lock( &g_RingRx._mutex );

            g_RingRx._wanted = 1;

            pthread_cond_wait( &g_RingRx._cond, &g_RingRx._mutex );
            pthread_mutex_unlock( &g_RingRx._mutex );

            continue;
         }

         break;
      }

      int theLen = 0;
      if( ( theLen = recv( theSock, I_elem->_payload[ I_elem->_count ], sizeof( I_elem->_payload[ I_elem->_count ] ), 0 ) ) > 0 )
      {
         I_elem->_len[ I_elem->_count++ ] = theLen;
      }
      else
      {
         I_elem->_len[ I_elem->_count ] = 0;
      }

      if( I_elem->_count == sizeof( I_elem->_len ) / sizeof( *I_elem->_len ) || g_RingRx._wanted )
      {
         ring_put_write_elem( &g_RingRx, I_elem );
      }
      else
      {
         RingElem* ret = __sync_val_compare_and_swap( &g_rx_elem, 0, I_elem );

         if( ret )
         {
            ring_put_write_elem( &g_RingRx, I_elem );
         }
      }

      ++g_RxCount;

      if( g_RingRx._wanted )
      {
         pthread_mutex_lock( &g_RingRx._mutex );

         g_RingRx._wanted = 0;

         pthread_cond_broadcast( &g_RingRx._cond );
         pthread_mutex_unlock( &g_RingRx._mutex );
      }
   }
   while( I_elem );

   return 0;
}

static RingElem* g_tx_elem = 0;

void ring_tx( uint8_t* aData, uint16_t aSize )
{
   if( !aSize )
   {
      return;
   }

   RingElem* theElem = 0;

   while( 1 )
   {
      theElem = __sync_val_compare_and_swap( &g_tx_elem, g_tx_elem, 0 );

      if( !theElem )
      {
         theElem = ring_get_write_elem( &g_RingTx );
      }

      if( !theElem )
      {
         ++g_PutGetFailCount;

         pthread_mutex_lock( &g_RingTx._mutex );

         g_RingTx._wanted = 1;

         pthread_cond_wait( &g_RingTx._cond, &g_RingTx._mutex );
         pthread_mutex_unlock( &g_RingTx._mutex );

         continue;
      }

      break;
   }

   memcpy( theElem->_payload[ theElem->_count ], aData, aSize );

   theElem->_len[ theElem->_count ] = aSize;

   ++theElem->_count;

   if( theElem->_count == sizeof( theElem->_len ) / sizeof( *theElem->_len ) || g_RingTx._wanted )
   {
      ring_put_write_elem( &g_RingTx, theElem );
   }
   else
   {
      RingElem* ret = __sync_val_compare_and_swap( &g_tx_elem, 0, theElem );

      if( ret )
      {
         ring_put_write_elem( &g_RingTx, theElem );
      }
   }


   if( g_RingTx._wanted )
   {
      pthread_mutex_lock( &g_RingTx._mutex );

      g_RingTx._wanted = 0;

      pthread_cond_broadcast( &g_RingTx._cond );
      pthread_mutex_unlock( &g_RingTx._mutex );
   }

   ++g_PutCount;

   if( 1 )
   {
      ring_debug_print();
   }
}

static void* ring_proc_thread( void* anArg )
{
   ProcessingHandler theHandler = ( ProcessingHandler )anArg;

   RingElem* I_elem = 0;

   int I_signal_guard = 0;

   do
   {
      while( 1 )
      {
         I_elem = ring_get_read_elem( &g_RingRx );

         if( !I_elem )
         {
            I_elem = __sync_val_compare_and_swap( &g_rx_elem, g_rx_elem, 0 );
         }

         if( !I_elem )
         {
            ++g_ProcGetFailCount;

            pthread_mutex_lock( &g_RingRx._mutex );

            if( g_RingRx._wanted )
            {
               pthread_cond_broadcast( &g_RingRx._cond );
            }
            else
            {
               g_RingRx._wanted = 1;
            }

            I_signal_guard = 0;

            pthread_cond_wait( &g_RingRx._cond, &g_RingRx._mutex );
            pthread_mutex_unlock( &g_RingRx._mutex );

            continue;
         }

         break;
      }

      if( theHandler )
      {
         int i;
         for( i = 0; i < I_elem->_count; ++i )
         {
            theHandler( I_elem->_payload[ i ], I_elem->_len[ i ] );
            I_elem->_len[ i ] = 0;

            ++g_ProcCount;
         }

         I_elem->_count = 0;
      }

      ring_put_read_elem( &g_RingRx, I_elem );

      if( !( ++I_signal_guard & ( RING_ELEMENT_COUNT / 4 - 1 ) ) )
      {
         if( g_RingRx._wanted )
         {
            pthread_mutex_lock( &g_RingRx._mutex );

            g_RingRx._wanted = 0;

            pthread_cond_broadcast( &g_RingRx._cond );
            pthread_mutex_unlock( &g_RingRx._mutex );
         }
      }
   }
   while( I_elem );

   return 0;
}

static void* ring_tx_thread( void* anArg )
{
   int theSock = ( int )anArg;

   RingElem* I_elem = 0;

   int I_signal_guard = 0;

   do
   {
      while( 1 )
      {
         I_elem = ring_get_read_elem( &g_RingTx );

         if( !I_elem )
         {
            I_elem = __sync_val_compare_and_swap( &g_tx_elem, g_tx_elem, 0 );
         }

         if( !I_elem )
         {
            ++g_TxGetFailCount;

            pthread_mutex_lock( &g_RingTx._mutex );

            if( g_RingTx._wanted )
            {
               pthread_cond_broadcast( &g_RingTx._cond );
            }
            else
            {
               g_RingTx._wanted = 1;
            }

            I_signal_guard = 0;

            pthread_cond_wait( &g_RingTx._cond, &g_RingTx._mutex );
            pthread_mutex_unlock( &g_RingTx._mutex );

            continue;
         }

         break;
      }

      int i;
      for( i = 0; i < I_elem->_count; ++i )
      {
         if( send( theSock, I_elem->_payload[ i ], I_elem->_len[ i ], 0 ) == I_elem->_len[ i ] )
         {
            ++g_TxCount;
         }
         else
         {
            fprintf( stdout, "ring_tx_thread: error %d\n", errno );
         }

         I_elem->_len[ i ] = 0;
      }

      I_elem->_count = 0;

      ring_put_read_elem( &g_RingTx, I_elem );

      if( !( ++I_signal_guard & ( RING_ELEMENT_COUNT / 4 - 1 ) ) )
      {
         if( g_RingTx._wanted )
         {
            pthread_mutex_lock( &g_RingTx._mutex );

            g_RingTx._wanted = 0;

            pthread_cond_broadcast( &g_RingTx._cond );
            pthread_mutex_unlock( &g_RingTx._mutex );
         }
      }
   }
   while( I_elem );

   return 0;
}

static void ring_create( Ring* aRing )
{
   pthread_spin_init( &aRing->_writer._lock, 0 );
   pthread_spin_init( &aRing->_reader._lock, 0 );

   pthread_mutex_t theMutex = PTHREAD_MUTEX_INITIALIZER;
   pthread_cond_t theCond = PTHREAD_COND_INITIALIZER;

   aRing->_mutex = theMutex;
   aRing->_cond = theCond;

   aRing->_writer._head._ptr = ( RingElem* )calloc( 1, sizeof( RingElem ) );
   aRing->_writer._head._counter = 0;
   aRing->_writer._head._ptr->_num = 0;

   RingPtr thePrev = aRing->_writer._head;

   int I_elem;
   for( I_elem = 1; I_elem < RING_ELEMENT_COUNT + 1; ++I_elem )
   {
      thePrev._ptr->_next._ptr = ( RingElem* )calloc( 1, sizeof( RingElem ) );
      thePrev._ptr->_next._counter = 0;
      thePrev._ptr->_next._ptr->_num = I_elem;

      thePrev = thePrev._ptr->_next;
   }

   aRing->_writer._tail = thePrev;
   aRing->_writer._tail._ptr->_num = I_elem;

   ++I_elem;

   aRing->_reader._head._ptr = ( RingElem* )calloc( 1, sizeof( RingElem ) );
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

   if( 1 )
   {
   pthread_create( &g_RxThreadId, 0, ring_rx_thread, ( void* )aSocket );
   pthread_create( &g_ProcThreadId, 0, ring_proc_thread, aHandler );
   }
   pthread_create( &g_TxThreadId, &theTxAttr, ring_tx_thread, ( void* )aSocket );

   return ret;
}

void ring_uninit()
{

}

static void ring_debug_print()
{
   if( !( g_PrintGuard++ % 1000000 ) )
   {
      printf( "put lc: %d, get lc: %d, pgf: %d, tgf: %d, prgf: %d, rgf: %d\n",
              g_PutLoopCount, g_GetLoopCount, g_PutGetFailCount, g_TxGetFailCount, g_ProcGetFailCount, g_RxGetFailCount );

      printf( "tx: %d, rx: %d, put: %d, proc: %d\n", g_TxCount, g_RxCount, g_PutCount, g_ProcCount );

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

   }
}
