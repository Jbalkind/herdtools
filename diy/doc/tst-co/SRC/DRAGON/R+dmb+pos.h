static void ass(FILE *out) {
  fprintf(out,"%s\n","@START _litmus_P1");
  fprintf(out,"%s\n","	mov r6,#3");
  fprintf(out,"%s\n","	str r6,[r1]");
  fprintf(out,"%s\n","	ldr ip,[r1]");
  fprintf(out,"%s\n","@START _litmus_P0");
  fprintf(out,"%s\n","	mov r2,#1");
  fprintf(out,"%s\n","	str r2,[r1]");
  fprintf(out,"%s\n","	dmb");
  fprintf(out,"%s\n","	mov r3,#2");
  fprintf(out,"%s\n","	str r3,[r1]");
}
