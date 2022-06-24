(* ultimate_tactics.mli is derived from coq/tactics/tactics.mli, extended with support for evaluating through opaque constants   *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(** {6 Reduction tactics. } *)

val reduce: ?cbv:bool -> Environ.env -> Evd.evar_map -> Evd.econstr -> Evd.evar_map * Evd.econstr
