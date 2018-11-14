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

(** Function values.

    @since 4.08 *)

external id : 'a -> 'a = "%identity"
(** [id] is the identity function. For any argument [x], [id x] is [x]. *)

val const : 'a -> (_ -> 'a)
(** [const c] is a function that always returns the value [c]. For any
    argument [x], [(const c) x] is [c]. *)

val flip : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)
(** [flip f] reverses the argument order of the binary function
    [f]. For any arguments [x] and [y], [(flip f) x y] is [f y x]. *)

val negate : ('a -> bool) -> ('a -> bool)
(** [negate p] is the negation of the predicate function [p]. For any
    argument [x], [(negate p) x] is [not (p x)]. *)

val protect : acquire:(unit -> 'a) -> finally:('a -> unit) -> ('a -> 'b) -> 'b
(** [protect ~acquire ~finally work] invokes [acquires], then [work],
   and then invokes [finally] when [work] returns with its value or an
   exception. In the latter case the exception is re-raised after
   [finally]. If [finally] raises an exception, then the exception
   [Finally] is raised instead, as documented below.

    [protect] lets you manage resources reliably, under the following
   conditions: 1) the acquisition either succeeds, or if it raises an
   exception then it is without having acquired the resource (strong
   exception safety); 2) the release of the resource never fails. If
   the conditions are met, then the resource is guaranteed to have
   been released when protect returns.

    Note: this does not yet protect against asynchronous exceptions
   raised inside [acquire] or [finally] by signal handlers, such as
   Sys.Break.

    @since 4.08.0 *)

exception Finally of { work : exn option; finally : exn; }
(** Raised by [protect ~acquire ~finally work] when [finally] raises
   an exception. The first exception argument is the one raised by
   [work], if any, and the second exception the one raised by
   [finally]. As a general rule, this exception should not be caught,
   it denotes a programming error and the code should be modified not
   to trigger it. *)

