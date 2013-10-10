/*********************************************************************/
/*                          Litmus                                   */
/*                                                                   */
/*        Luc Maranget, INRIA Paris-Rocquencourt, France.            */
/*        Susmit Sarkar, University of Cambridge, UK.                */
/*                                                                   */
/*  Copyright 2010 Institut National de Recherche en Informatique et */
/*  en Automatique and the authors. All rights reserved.             */
/*  This file is distributed  under the terms of the Lesser GNU      */
/*  General Public License.                                          */
/*********************************************************************/

#include <stdio.h>
#include <sched.h>
#include <unistd.h>
#include <inttypes.h>
#include <errno.h>
#include "utils.h"
#include "affinity.h"

#if 0
static void pp_set(FILE *fp, cpus_t *p) {
  for (int k = 0 ; k < p->sz ; k++) {
    fprintf(fp," %i", p->cpu[k]) ;
  }
}
#endif

cpus_t *read_affinity(void) {
  cpu_set_t mask;
  int sz = 0 ;
  int res = pthread_getaffinity_np(pthread_self(), sizeof(mask), &mask) ;
  
  if (res != 0) { 
    errno = res ;
    err(res,"pthread_getaffinity_np");
  }
  for (int p=0 ; p <  CPU_SETSIZE ; p++) {
    if (CPU_ISSET(p,&mask)) sz++ ;
  }

  cpus_t *r = cpus_create(sz) ;
  for (int p=0, *q=r->cpu ; p <  CPU_SETSIZE ; p++) {
    if (CPU_ISSET(p,&mask)) *q++ = p ;
  }
  return r ;
}

/* Attempt to force processors wake up, on devices where unused procs
   go to sleep... */


static void* loop(void *p)  {
  int *q = p ;
  intptr_t r1 = 0, r2=0 ;
  for (int k = *q ; k >  0 ; k--) { r1 += k ; r2 += k ; }
  return (void *)(r1-r2) ;
}

static void warm_up(int sz, int max) {
    pthread_t th[sz];
    for (int k = 0 ; k < sz ; k++) launch(&th[k], loop, &max) ;
    for (int k = 0 ; k < sz ; k++) join(&th[k]) ;
}

static const int lim_max  = 1000000 ;

cpus_t *read_force_affinity(int n_avail, int verbose) {
  int sz = n_avail <= 1 ? 1 : n_avail ;
  int max = 4 ;

  for ( ; ; ) {
    warm_up(sz+1,max) ;
    cpus_t *r = read_affinity() ;
    if (n_avail <= r->sz) return r ;
    if (verbose) {
      fprintf(stderr,"Read affinity: '") ;
      cpus_dump(stderr,r) ;
      fprintf(stderr,"'\n") ;
    }
    max = max >= lim_max ? max : 2*max ;
    cpus_free(r) ;
  }
}

/* Enforcing processor affinity.
   Notice that logical processor numbers may be negative.
   In that case, affinity setting is ignored */
 
void write_affinity(cpus_t *p) {
  cpu_set_t mask;
  int exists_pos = 0 ;

  CPU_ZERO(&mask) ;
  for (int k = 0 ; k < p->sz ; k++) {
    if (p->cpu[k] >= 0) {
      CPU_SET(p->cpu[k],&mask) ;
      exists_pos = 1 ;
    }
  }
  if  (exists_pos) {
    int r = pthread_setaffinity_np(pthread_self(),sizeof(mask),&mask) ;
    if (r != 0) {
      errno = r ;
      err(r,"pthread_setaffinity_np") ;
    }
  }
}

void write_one_affinity(int a) {
  if (a >= 0) {
    cpu_set_t mask;
    CPU_ZERO(&mask) ;
    CPU_SET(a,&mask) ;
    int r = pthread_setaffinity_np(pthread_self(), sizeof(mask), &mask) ;
    if (r != 0) {
      errno = r ;
      err(r,"pthread_setaffinity_np") ;
    }
  }
}

void force_one_affinity(int a, int sz,int verbose, char *name) {
  if (a >= 0) {
    cpu_set_t mask;
    int r ;
    int max = 4 ;
    CPU_ZERO(&mask) ;
    CPU_SET(a,&mask) ;
    do {
      r = pthread_setaffinity_np(pthread_self(), sizeof(mask), &mask) ;
      if (r != 0) {
        if (verbose) fprintf(stderr,"%s: force %i failed\n",name,a) ;
        warm_up(sz+1,max) ;
        max = max >= lim_max ? max : 2*max ;
      }
    } while (r != 0) ;
  }
}