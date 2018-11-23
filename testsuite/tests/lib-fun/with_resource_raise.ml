(* TEST
*)

(* Ensure that the program terminates if an exception in ~release is
   uncaught *)
let _ =
  let raise_in_release () =
    let id () = () in
    let f () = raise Exit in
    Fun.with_resource ~acquire:id ~release:f id
  in
  (* reset exit code *)
  at_exit (fun () -> exit 0);
  (try raise_in_release () with _ -> ());
  print_endline "Fail"
