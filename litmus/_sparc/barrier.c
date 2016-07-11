/**********************/
/* User level barrier */
/**********************/


typedef struct {
  volatile int c,sense;
  int n ;
} sense_t;

static void barrier_init (sense_t *p,int n) {
  p->n = p->c = n;
  p->sense = 0;
}

static void barrier_wait(sense_t *p) {
  int sense = p->sense ;
  int r1, r2, r3, r4;
asm __volatile (
        setx    [s], r1, r2
	setx    [c], r1, r4
!	sll	global_cnt_reg, 0x3, r1
!	add	r1, r2, r2
bloop1:						! get lock of barrier count
        mov     0xff, r1
        cas     [r2], %g0, r1
        brnz    r1, bloop1
        nop

        ld      [r4], r3		! increment
        inc     r3
        st      r3, [r4]

        st      %g0, [r2]          		! unlock

bloop2: 					! check the barrier count
        ld      [r4], r3		! if 0 ->
        brz     r3, bout2  		  	! somebody already reset it
        sub     r3, [n], r3	! subtract THREAD_COUNT
        brnz    r3, bloop2      		! if 0 -> we are out.
        nop
        
        st      %g0, [r4] 		! clear the barrier counter
bout2:
        nop

: [r1] "=&r" (r1),  [r2] "=&r" (r2),  [r3] "=&r" (r3),  [r4] "=&r" (r4)
: [c] "r" (&p->c), [s] "r" (&p->sense), [n] "r" (p->n)
: [r1] "=&r" (r1),  [r2] "=&r" (r2),  [r3] "=&r" (r3),  [r4] "=&r" (r4),  "memory") ;
}
