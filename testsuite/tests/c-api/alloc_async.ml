(* TEST
 modules = "alloc_async_stubs.c";
*)

(* Ensure that finalisers (asynchronous callbacks) do not execute inside C code.
   The C stub itself contains more details on the mechanism. *)

external test : int ref -> unit = "stub"
external print_status : string -> int -> unit = "print_status_caml" [@@noalloc]

let f () =
  let r = ref 42 in
  Gc.finalise (fun s -> r := !s) (ref 17);
  print_status "OCaml, before" !r;
  test r;
  print_status "OCaml, after" !r;
  ignore (Sys.opaque_identity (ref 100));
  print_status "OCaml, after alloc" !r;
  ()

let () = (f [@inlined never]) ()
