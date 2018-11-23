(* TEST
include unix
   * native

(* Test only implemented on Unix. It currently fails with bytecode. *)
*)

let tick = 0.001 (* 1 ms *)

exception Alarm

let block, unblock =
  let set x () =
    try ignore (Unix.sigprocmask x [Sys.sigalrm])
    with Alarm -> ()
  in
  set Unix.SIG_BLOCK, set Unix.SIG_UNBLOCK

let _ =
  let handle _ = raise Alarm in
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle handle);
  block ()

let time = Unix.gettimeofday

let command ppid =
  while true do
    Unix.sleepf tick;
    Unix.kill ppid Sys.sigalrm
  done

type pass = Pass | Fail

let report b =
  print_string (if b == Pass then "Passed\n" else "Failed\n")

let if_unix, fork, kill =
  if Sys.os_type = "Unix" then
    (fun f -> f), Unix.fork, Unix.kill
  else
    (* not implemented *)
    (fun _ _ -> report Pass), (fun () -> 1), (fun _ _ -> ())

let check_receive_signal () =
  let _ =
    try
      unblock ();
      let start = time () in
      let x = ref (0,1) in
      while (time ()) -. start < 20. *. tick do
        x := match !x with (a,b) -> (b,a);
      done;
      ignore (Sys.opaque_identity !x);
      report Fail;
    with
      Alarm -> report Pass
  in
  block ()

let block_signal tock =
  let start = time () in
  while (time ()) -. start < tock do () done

let check_block_signal () =
  unblock ();
  let res =
    try block_signal (10. *. tick) ; Pass
    with Alarm -> Fail
  in
  block ();
  report res

let test_with_resource b x f =
  let tock = 2.1 *. tick in
  Fun.with_resource
    ~acquire:(fun () -> incr x ; if b then block_signal tock)
    ~release:(fun () -> if not b then block_signal tock ; decr x)
    f

let repeat_test_with_resource f =
  let start = time () in
  let tock = 150. *. tick in
  let x = ref 0 in
  let y = ref 0 in
  let _ =
    try
      unblock ();
      while (time ()) -. start < tock do
        (try test_with_resource true x f with _ -> ());
        (try test_with_resource false y f with _ -> ())
      done;
      block ();
    with _ -> block ()
  in
  report (if !x = 0 && !y = 0 then Pass else Fail)

let test_signal pid =
  print_endline "Control 1:";
  if_unix check_receive_signal ();
  print_endline "Control 2:";
  if_unix check_block_signal ();
  print_endline "Test 1:";
  if_unix repeat_test_with_resource (fun () -> block_signal tick);
  print_endline "Test 2:";
  if_unix repeat_test_with_resource (fun () -> ());
  print_endline "Test 3:";
  if_unix repeat_test_with_resource (fun () -> raise Exit);
  print_endline "Test 4:";
  if_unix repeat_test_with_resource Unix.pause;
  kill pid Sys.sigkill

let _ =
  try
    Printexc.record_backtrace true;
    match fork () with
    | 0 -> command (Unix.getppid ())
    | pid -> test_signal pid
  with e -> Printexc.print_backtrace stderr; raise e
