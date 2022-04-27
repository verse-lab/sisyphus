(** Opaque representation of Coq libraries *)
type t

(** [make ~path name] creates a coq library from a [path] (to the .vo
   files) and the library [name] (assumes -R recursive) *)
val make : path:Fpath.t -> string -> t

(** [path coqlib] returns the physical path to the Coq library.  *)
val path : t -> Fpath.t

(** [to_load_path lib] converts a coq library into a loadable path *)
val to_load_path : t -> Loadpath.vo_path
