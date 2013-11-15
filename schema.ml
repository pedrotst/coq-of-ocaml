type t = {
  variables : Name.t list;
  typ : Type.t}

let of_type_expr (typ : Types.type_expr) : t =
  let typ = Type.of_type_expr typ in
  { variables = Name.Set.elements (Type.free_vars typ); typ = typ }

(** Rename the type variables starting from the letter 'A'. *)
let rename_nicely (schema : t) : t =
  let rec aux s x' : t =
    match s.variables with
    | [] -> s
    | x :: xs ->
      let s = aux { variables = xs; typ = s.typ } (Char.chr (Char.code x' + 1)) in
      { variables = String.make 1 x' :: s.variables; typ = Type.substitute_variable s.typ x (String.make 1 x') } in
  aux schema 'A'

let of_expression (e : Typedtree.expression) : t =
  rename_nicely (of_type_expr e.Typedtree.exp_type)
