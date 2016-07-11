module type S =
  sig
    type a (* Native arch barrier *)
    type b = MEMBAR (* SPARC Memory barrier *)
    val a_to_b : a -> b
  end
