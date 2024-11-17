open Lib.Eval_4

let test_alpha =
  Abs ("x", Add (Var "x", IfZero (Var "x", Int 1, Int 0)))

let alpha_result = alphaconv test_alpha []
let () =
  print_endline ("Avant alpha-conversion : " ^ print_term test_alpha);
  print_endline ("Après alpha-conversion : " ^ print_term alpha_result)

let term1 = Abs ("x", Let ("y", Var "x", Add (Var "y", Var "x")))
let () =
  print_endline ("Avant alpha-conversion : " ^ print_term term1);
  print_endline ("Après alpha-conversion : " ^ print_term (alphaconv term1 []))
let term2 = Fix (Abs ("f", Abs ("x", IfZero (Var "x", Int 1, App (Var "f", Sub (Var "x", Int 1))))))
let () =
  print_endline ("Avant alpha-conversion : " ^ print_term term2);
  print_endline ("Après alpha-conversion : " ^ print_term (alphaconv term2 []))

let test_subst =
  Add (Var "x", Sub (Var "y", Int 5))

let subst_result = substitution "x" (Int 42) test_subst
let () =
  print_endline ("Avant substitution : " ^ print_term test_subst);
  print_endline ("Après substitution : " ^ print_term subst_result)

let add_example = Add (Int 3, Int 4) (* 3 + 4 *)
let sub_example = Sub (Int 10, Int 3) (* 10 - 3 *)

(* Liste *)
let list_example = List [Int 1; Int 2; Int 3] (* [1; 2; 3] *)
let head_example = Head list_example (* head([1; 2; 3]) *)
let tail_example = Tail list_example (* tail([1; 2; 3]) *)

let ifzero_example = IfZero (Int 0, Int 1, Int 2) (* ifZero(0, 1, 2) *)
let ifempty_example = IfEmpty (List [], Int 1, Int 2) (* ifEmpty([], 1, 2) *)

(*calcul de factoriel*)
(*fonction de multiplication de deux entiers*)
let mul = Fix (Abs ("mul", Abs ("x", Abs ("y", IfZero (Var "x", Int 0, Add (Var "y", App (App (Var "mul", Sub (Var "x", Int 1)), Var "y")))))))
let factoriel = Fix (Abs ("f", Abs ("n", IfZero (Var "n", Int 1, App (App (mul, Var "n"), App (Var "f", Sub (Var "n", Int 1)))))))
let fact_3 = App (factoriel, Int 3) (* 3! *)
let fact_5 = App (factoriel, Int 5) (* 5! *)

(* let x = 42 in x + 10 *)

let let_example = Let ("x", Int 42, Add (Var "x", Int 10)) (* let x = 42 in x + 10 *)

let () =
  let test_terms = [add_example; sub_example; list_example; head_example; tail_example; ifzero_example; ifempty_example; fact_3; fact_5; let_example] in
  List.iteri (fun i t ->
    print_endline ("Terme " ^ string_of_int i ^ " : " ^ print_term t);
    match ltr_cbv_norm_timeout t 1.0 with
    | t' -> print_endline ("Réduction : " ^ print_term t')
    | exception Timeout -> print_endline "Timeout") test_terms
