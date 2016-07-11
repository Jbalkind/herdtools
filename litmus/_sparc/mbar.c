inline static void mbar(void) {
  asm __volatile__ ("membar #StoreLoad" ::: "memory");
}
