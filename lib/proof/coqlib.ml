type t = (Fpath.t * string)

let make ~path name = (path, name)

let path (path, _) = path

let to_load_path ((path, name) : t) =
  Loadpath.{
    unix_path=Fpath.to_string path;
    coq_path = Names.DirPath.make [Names.Id.of_string name];
    implicit=true;
    has_ml=true;
    recursive=true;
  }
