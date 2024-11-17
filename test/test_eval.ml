open Lib.Eval_4

(* Identité : I = λx.x *)
let i = Abs ("x", Var "x")

(* Combinateur K = λx.λy.x *)
let k = Abs ("x", Abs ("y", Var "x"))

(* Combinateur S = λx.λy.λz.(x z) (y z) *)
let s = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z")))))

(* Expression complexe : SKK *)
let skk = App (App (s, k), k)

(* Expression complexe : SII *)
let sii = App (App (s, i), i)

(* delta *)
let delta = Abs ("x", App (Var "x", Var "x"))

(* omega *)
let omega = App (delta, delta)

let test_terms = [
  ("i", i);
  ("k", k);
  ("s", s);
  ("skk", skk);
  ("sii", sii);
  ("omega", omega)
]

let () =
  List.iter (fun (name, t) -> 
    print_endline ("Term: " ^ name);
    let reduced = ltr_cbv_norm_timeout t 1. in
    print_endline ("Reduced: " ^ (print_term reduced));
  ) test_terms
  
