#indent "off"
(* customized version of Map *)
module M
(* module M =
  Map.Make
    (struct
      type t = Id.t
      let compare = compare
    end)
include M *)

let add_list xys (env:Map<'a,'b>) = List.fold (fun (env:Map<'a,'b>) (x, y) -> env.Add(x, y)) env xys
let add_list2 xs ys (env:Map<'a,'b>) = List.fold2 (fun (env:Map<'a,'b>) x y -> env.Add(x, y)) env xs ys
