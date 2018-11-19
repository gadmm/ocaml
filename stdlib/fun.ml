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

exception Release_raised of exn

let protect ~acquire ~(release : _ -> unit) work =
  let release_no_exn resource =
    try release resource with e ->
      let bt = Printexc.get_raw_backtrace () in
      Printexc.raise_with_backtrace (Release_raised e) bt
  in
  let resource = acquire () in
  match work resource with
  | result -> release_no_exn resource ; result
  | exception work_exn ->
      let work_bt = Printexc.get_raw_backtrace () in
      release_no_exn resource ;
      Printexc.raise_with_backtrace work_exn work_bt
