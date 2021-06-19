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
external create: unit -> t = "caml_mutex_new"
external lock: t -> unit = "caml_mutex_lock"
external try_lock: t -> bool = "caml_mutex_try_lock"
external unlock: t -> unit = "caml_mutex_unlock"

(*
  Critical sections are enforced due to:
   - Mutex.lock does not poll on leaving the blocking section
     since 4.12.
   - Never inline, to avoid theoretically-possible reorderings with
     flambda.
   - We inline the call to Mutex.unlock to avoid polling in bytecode
     mode.
*)
let[@poll explicit] with_lock m ~scope =
  let () = lock m (* BEGIN ATOMIC *) in
  match (* END ATOMIC *) scope () with
  | (* BEGIN ATOMIC *) x -> unlock m ; (* END ATOMIC *) x
  | (* BEGIN ATOMIC *) exception e -> unlock m ; (* END ATOMIC *) raise e
