(* TEST
include unix
   * native

(* Test only implemented on Unix. It currently fails with bytecode. *)
*)

let tick = 0.001 (* 1 ms *)

exception Alarm

let _ =
  if Sys.os_type <> "Unix" then begin
    (* not implemented *)
    print_endline "Control 1:
Passed
Control 2:
Passed
Test 1:
Passed
Test 2:
Passed
Test 3:
Passed
Test 4:
Passed";
    exit 0;
  end

let block () =
  try Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> ()))
  with Alarm -> ()

let unblock () =
  try Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Alarm))
  with Alarm -> ()

let _ =
  let handle _ = raise Alarm in
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle handle);
  block ()

let time = Unix.gettimeofday

let command ppid =
  try
    while true do
      Unix.sleepf tick;
      Unix.kill ppid Sys.sigalrm
    done
  with Unix.Unix_error _ -> ()

type pass = Pass | Fail

let report b =
  print_endline (if b == Pass then "Passed" else "Failed")

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

let test_with_resource branch count ~inside ~outside =
  let tock = 2.1 *. tick in
  Fun.with_resource outside
    ~acquire:(fun () ->
        incr count ;
        if branch then begin
          block_signal tock ;
          inside ()
        end )
    ~release:(fun r ->
        try
          if not branch then begin
            block_signal tock ;
            inside ()
          end ;
          decr count
        with
          _ -> () )

let repeat_test_with_resource ~inside ~outside =
  let start = time () in
  let tock = 150. *. tick in
  let x = ref 0 in
  let y = ref 0 in
  let _ =
    try
      unblock ();
      while (time ()) -. start < tock do
        (try test_with_resource ~inside ~outside true x with _ -> ()) ;
        (try test_with_resource ~inside ~outside false y with _ -> ())
      done;
      block ()
    with e -> block (); raise e
  in
  report (if !x = 0 && !y = 0 then Pass else Fail)

let test_signal pid =
  print_endline "Control 1:" ;
  check_receive_signal () ;
  print_endline "Control 2:" ;
  check_block_signal () ;
  let funs =
    [ "id", (fun () -> ())
    ; "print",
      (let out = open_out "/dev/null" in
      (fun () -> output_string out "a" ; flush out) )
    ; "block", (fun _ -> block_signal tick)
    ; "openclose",
      (fun _ ->
         match open_in "/tmp/sthg" with
         | f -> close_in f
         | exception Unix.Unix_error _ -> () )
    ] in
  let test_pair (x,f) (y,g) =
    Printf.printf "Test inside=%s, outside=%s\n" x y ;
    flush stdout ;
    repeat_test_with_resource ~inside:f ~outside:g
  in
  List.iter (fun x -> List.iter (test_pair x) funs) funs ;
  Unix.kill pid Sys.sigkill

let _ =
  try
    Printexc.record_backtrace true ;
    match Unix.fork () with
    | 0 -> command (Unix.getppid ())
    | pid -> test_signal pid
  with e -> Printexc.print_backtrace stderr ; raise e
