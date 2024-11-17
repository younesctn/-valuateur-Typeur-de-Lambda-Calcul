open Lib.Type


let print_equa (eq : equa) : string =
  let print_pair (t1, t2) = "(" ^ (print_type t1) ^ ", " ^ (print_type t2) ^ ")" in
  "[" ^ (String.concat "; " (List.map print_pair eq)) ^ "]"

(* Tests *)
let tests = [
  ("Identité", Abs ("x", Var "x"), []);
  ("Constante", Abs ("x", Abs ("y", Var "x")), []);
  ("Application simple", App (Var "f", Var "x"),
   [("f", Arr (Vart "α", Vart "α")); ("x", Vart "α")]);
  ("Composition", Abs ("f", Abs ("g", Abs ("x", App (Var "f", App (Var "g", Var "x"))))), []);
  ("Double application", Abs ("f", App (Var "f", App (Var "f", Var "x"))),
   [("x", Vart "α")]);
  ("Retourne une fonction", Abs ("x", Abs ("y", Var "y")), []);
  ("Applique une fonction", Abs ("x", Abs ("y", App (Var "x", Var "y"))), []);
]

(* Fonction pour lancer les tests *)
let run_tests tests =
  List.iter (fun (name, term, env) ->
    try
      Printf.printf "Test %s\n" name;
      Printf.printf "Terme : %s\n" (print_term term);
      Printf.printf "Equations : %s\n" (print_equa (genere_equa term (Vart "α") env));
      let inferred_type = infere_type term env 2.0 in
      Printf.printf "Type : %s\n" (print_type inferred_type)
    with
    | _ -> Printf.printf "%s : Erreur\n" name
  ) tests;;

(* Lancer les tests *)
run_tests tests
