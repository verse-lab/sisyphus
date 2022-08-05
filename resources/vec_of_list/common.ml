type 'a t = {
  mutable size : int;
  mutable vec : 'a array;
}

let create () = {
  size = 0;
  vec = [| |];
}

let create_with ~capacity x = {
  size = 0;
  vec = Array.make capacity x;
}

let return x = {
  size=1;
  vec= [| x |];
}

let push_unsafe v x =
  Array.set v.vec v.size x;
  v.size <- v.size + 1
