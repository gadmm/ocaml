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

type raw_backtrace
external get_raw_backtrace:
  unit -> raw_backtrace = "caml_get_exception_raw_backtrace"
external raise_with_backtrace: exn -> raw_backtrace -> 'a
  = "%raise_with_backtrace"

exception Release_failure of exn

let protect ~acquire ~release work =
  let release_no_exn resource =
    try release resource with e ->
      let finally_bt = get_raw_backtrace () in
      raise_with_backtrace (Release_failure e) finally_bt
  in
  let resource = acquire () in
  match work resource with
  | result -> release_no_exn resource ; result
  | exception work_exn ->
      let work_bt = get_raw_backtrace () in
      release_no_exn resource ;
      raise_with_backtrace work_exn work_bt
