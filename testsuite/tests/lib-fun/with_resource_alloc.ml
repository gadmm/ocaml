(* TEST
   * native
*)

let count_alloc f =
  let gc_before_stat = Gc.stat () in
  (* unreliable in bytecode: *)
  let gc_before_minor = Gc.minor_words () in
  f ();
  let gc_after = Gc.stat () in
  let result =
    if gc_after =
       { gc_before_stat with minor_words = gc_before_minor }
    then "Passed" else "Failed"
  in
  print_endline result

let _ =
  let rec loop n = if n = 0 then () else loop (n - 1) in
  let loop () = loop 10 in
  let test () = Fun.with_resource ~acquire:loop ~release:loop loop in
  print_endline "Control:";
  count_alloc (fun () -> ());
  print_endline "Test:";
  count_alloc test
