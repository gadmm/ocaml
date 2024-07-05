(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Xavier Leroy and Pascal Cuoq, INRIA Rocquencourt             *)
(*                                                                        *)
(*   Copyright 1995 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type t
external create: unit -> t = "caml_ml_mutex_new"
external lock: t -> unit = "caml_ml_mutex_lock"
external try_lock: t -> bool = "caml_ml_mutex_try_lock"
external unlock: t -> unit = "caml_ml_mutex_unlock"

(* private re-export *)
external reraise : exn -> 'a = "%reraise"

(* The following functions are carefully written to be correct wrt.
   asynchronous exceptions, by reasoning about polling points present
   in the code.

   - We use [@inline never] to prevent flambda from moving a safepoint
     from the surrounding code to the wrong place.

   - [unlock] being an external, this function call does not poll in
     bytecode. *)

let[@inline never] protect m f =
  lock m;
  match f() with
  | x -> unlock m; x
  | exception e -> unlock m; reraise e

let[@inline never] try_protect m f =
  if try_lock m then
    match f () with
    | x -> unlock m; Some x
    | exception e -> unlock m; reraise e
  else
    None
