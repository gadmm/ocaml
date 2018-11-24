(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                         The OCaml programmers                          *)
(*                                                                        *)
(*   Copyright 2018 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

external id : 'a -> 'a = "%identity"
let const c _ = c
let flip f x y = f y x
let negate p v = not (p v)

exception Finally_raised of exn

let protect ~(finally : unit -> unit) work =
  let finally_no_exn () =
    try finally () with e -> raise (Finally_raised e)
  in
  match work () with
  | result -> finally_no_exn () ; result
  | exception work_exn ->
      let work_bt = Printexc.get_raw_backtrace () in
      finally_no_exn () ;
      Printexc.raise_with_backtrace work_exn work_bt

let with_resource_native ~acquire ~(release : _ -> unit) work =
  let release_no_exn release resource =
    try Printexc.catch release resource
    with _ -> exit 2 (* printing error message failed *)
  in
  let resource = acquire () in
  (* no allocs : critical section for asynchronous exceptions *)
  match work resource with
  | result -> release_no_exn release resource ; result
  | exception e -> release_no_exn release resource ; raise e

let set_mask sigs = Unix.(sigprocmask SIG_SETMASK) sigs

let all_sigs = Sys.([sigabrt; sigalrm; sigfpe; sighup;
                     sigill; sigint; sigkill; sigpipe;
                     sigquit; sigsegv; sigterm; sigusr1;
                     sigusr2; sigchld; sigcont; sigstop;
                     sigtstp; sigttin; sigttou; sigvtalrm;
                     sigprof; sigbus; sigpoll; sigsys;
                     sigtrap; sigurg; sigxcpu; sigxfsz])

(* Broken *)
let with_resource_bytecode ~acquire ~(release : _ -> unit) work =
  let release_no_exn release resource =
    let old_mask = set_mask all_sigs (* native: allocates *) in
    let _ =
      try Printexc.catch release resource
      with _ -> exit 2 (* printing error message failed *)
    in
    ignore (set_mask old_mask)
  in
  let old_mask = set_mask all_sigs in
  let resource = try acquire () with e -> ignore (set_mask old_mask); raise e in
  (* no allocs : critical section for asynchronous exceptions *)
  match
    ignore (set_mask old_mask);
    work resource
  with
  | result -> release_no_exn release resource ; result
  | exception e -> release_no_exn release resource ; raise e

let with_resource =
  if Sys.os_type = "Unix" && Sys.backend_type = Sys.Bytecode
  then with_resource_bytecode
  else with_resource_native
