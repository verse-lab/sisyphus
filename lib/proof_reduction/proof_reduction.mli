type filter =
  path:string ->
  label:string ->
  [ `Unfold | `KeepOpaque | `Subst of Names.Constant.t ]
(** a [filter] is a function that informs the reduction mechanism how
   to handle opaque constants:

     - [`Unfold] the constant by retrieving its definition if it
       exists.

     - [`KeepOpaque] and don't expand the constant

     - [`Subst replacement] replace the constant with a replacement
       constant that is transparent instead.  *)

val reduce :
  ?filter:filter ->
  ?cbv:bool ->
  Environ.env -> Evd.evar_map -> Evd.econstr -> Evd.evar_map * Evd.econstr
