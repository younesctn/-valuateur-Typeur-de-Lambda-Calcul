(* Définition du type pour représenter les termes du lambda-calcul *)
type pterm =
  | Var of string                   (* Variable *)
  | App of pterm * pterm            (* Application *)
  | Abs of string * pterm           (* Abstraction *)
  | Int of int                      (* Entier naturel *)
  | Add of pterm * pterm            (* Addition *)
  | Sub of pterm * pterm            (* Soustraction *)
  | List of pterm list              (* Liste *)
  | Cons of pterm * pterm           (* Construction de liste ? *)
  | Head of pterm                   (* Tête de liste *)
  | Tail of pterm                   (* Queue de liste *)
  | IfZero of pterm * pterm * pterm (* Test si zéro *)
  | IfEmpty of pterm * pterm * pterm (* Test si liste vide *)
  | Fix of pterm                    (* Opérateur de point fixe *)
  | Let of string * pterm * pterm   (* Let natif *)

(* Fonction pour convertir un terme en chaîne de caractères lisible *)
let rec print_term (t : pterm) : string =
  match t with
  | Var x -> x
  | App (t1, t2) -> "(" ^ print_term t1 ^ " " ^ print_term t2 ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ print_term t ^ ")"
  | Int n -> string_of_int n
  | Add (t1, t2) -> "(" ^ print_term t1 ^ " + " ^ print_term t2 ^ ")"
  | Sub (t1, t2) -> "(" ^ print_term t1 ^ " - " ^ print_term t2 ^ ")"
  | List ts -> "[" ^ String.concat "; " (List.map print_term ts) ^ "]"
  | Cons (t1, t2) -> "(" ^ print_term t1 ^ " :: " ^ print_term t2 ^ ")"
  | Head t -> "head(" ^ print_term t ^ ")"
  | Tail t -> "tail(" ^ print_term t ^ ")"
  | IfZero (cond, t1, t2) -> "ifZero(" ^ print_term cond ^ ", " ^ print_term t1 ^ ", " ^ print_term t2 ^ ")"
  | IfEmpty (cond, t1, t2) -> "ifEmpty(" ^ print_term cond ^ ", " ^ print_term t1 ^ ", " ^ print_term t2 ^ ")"
  | Fix t -> "fix(" ^ print_term t ^ ")"
  | Let (x, t1, t2) -> "let " ^ x ^ " = " ^ print_term t1 ^ " in " ^ print_term t2

(* Compteur global pour générer des noms de variables uniques *)
let compteur_var = ref 0

(* Génère un nouveau nom de variable unique préfixé par "X" *)
let nouvelle_var () : string =
  compteur_var := !compteur_var + 1;
  "X" ^ string_of_int !compteur_var

(* Effectue l'α-conversion : renomme les variables liées pour éviter les conflits *)
let rec alphaconv (t : pterm) (env : (string * string) list) : pterm =
  match t with
  | Var x -> (
      (* Si la variable est dans l'environnement, on la renomme *)
      match List.assoc_opt x env with
      | Some new_x -> Var new_x
      | None -> Var x)
  | Abs (x, body) ->
      (* Renommer la variable liée et mettre à jour l'environnement *)
      let new_x = nouvelle_var () in
      let new_env = (x, new_x) :: env in
      Abs (new_x, alphaconv body new_env)
  | App (t1, t2) ->
      (* Appliquer l'alpha-conversion aux sous-termes *)
      App (alphaconv t1 env, alphaconv t2 env)
  | Fix t1 ->
      (* Appliquer l'alpha-conversion au terme à l'intérieur de Fix *)
      Fix (alphaconv t1 env)
  | Let (x, e1, e2) ->
      (* Renommer la variable introduite par Let *)
      let new_x = nouvelle_var () in
      let new_env = (x, new_x) :: env in
      Let (new_x, alphaconv e1 env, alphaconv e2 new_env)
  | Int n -> Int n
  | Add (t1, t2) -> Add (alphaconv t1 env, alphaconv t2 env)
  | Sub (t1, t2) -> Sub (alphaconv t1 env, alphaconv t2 env)
  | List ts -> List (List.map (fun t -> alphaconv t env) ts)
  | Cons (t1, t2) -> Cons (alphaconv t1 env, alphaconv t2 env)
  | Head t -> Head (alphaconv t env)
  | Tail t -> Tail (alphaconv t env)
  | IfZero (cond, t1, t2) ->
      IfZero (alphaconv cond env, alphaconv t1 env, alphaconv t2 env)
  | IfEmpty (cond, t1, t2) ->
      IfEmpty (alphaconv cond env, alphaconv t1 env, alphaconv t2 env)

(* Effectue la substitution [x -> n]t : remplace x par n dans t *)
let rec substitution (x : string) (n : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then n else t
  | Abs (y, body) ->
      if y = x then Abs (y, body)
      else Abs (y, substitution x n body)
  | App (t1, t2) -> App (substitution x n t1, substitution x n t2)
  | Let (y, e1, e2) ->
      if y = x then Let (y, substitution x n e1, e2)
      else Let (y, substitution x n e1, substitution x n e2)
  | Fix f -> Fix (substitution x n f)
  | Add (t1, t2) -> Add (substitution x n t1, substitution x n t2)
  | Sub (t1, t2) -> Sub (substitution x n t1, substitution x n t2)
  | List ts -> List (List.map (fun t -> substitution x n t) ts)
  | Cons (t1, t2) -> Cons (substitution x n t1, substitution x n t2) (* pas sûr *)
  | Head t -> Head (substitution x n t)
  | Tail t -> Tail (substitution x n t)
  | IfZero (cond, t1, t2) ->
      IfZero (substitution x n cond, substitution x n t1, substitution x n t2)
  | IfEmpty (cond, t1, t2) ->
      IfEmpty (substitution x n cond, substitution x n t1, substitution x n t2)
  | Int _ -> t

(* Effectue une étape de réduction en stratégie call-by-value de gauche à droite *)
let rec ltr_cbv_step (t : pterm) : pterm option =
  match t with
  (* Réduction des applications *)
  | Abs (x,body) -> (
      match ltr_cbv_step body with
      | Some body' -> Some (Abs (x,body'))
      | None -> None)
  | App (Abs (x,body), t2) -> (match ltr_cbv_step t2 with
      | Some t2' -> Some (substitution x t2' body)
      | None -> Some (substitution x t2 body))
  | App (t1,t2) -> (match ltr_cbv_step t1 with
      | Some t1' -> Some (App (t1',t2))
      | None -> match ltr_cbv_step t2 with
          | Some t2' -> Some (App (t1,t2'))
          | None -> None)
  (* Réduction des additions *)
  | Add (Int n1, Int n2) -> Some (Int (n1 + n2))
  | Add (t1, t2) when is_value t1 -> (
      match ltr_cbv_step t2 with
      | Some t2' -> Some (Add (t1, t2'))
      | None -> None)
  | Add (t1, t2) -> (
      match ltr_cbv_step t1 with
      | Some t1' -> Some (Add (t1', t2))
      | None -> None)
  (* Réduction des soustractions *)
  | Sub (Int n1, Int n2) -> Some (Int (n1 - n2))
  | Sub (t1, t2) when is_value t1 -> (
      match ltr_cbv_step t2 with
      | Some t2' -> Some (Sub (t1, t2'))
      | None -> None)
  | Sub (t1, t2) -> (
      match ltr_cbv_step t1 with
      | Some t1' -> Some (Sub (t1', t2))
      | None -> None)
  (* Réduction des listes *)
  | Head (List (h :: _)) -> Some h
  | Head _ -> None
  | Tail (List (_ :: t)) -> Some (List t)
  | Tail _ -> None
  (* Réduction des conditionnelles *)
  | IfZero (Int 0, t1, _) -> Some t1
  | IfZero (Int _, _, t2) -> Some t2
  | IfZero (cond, t1, t2) -> (
      match ltr_cbv_step cond with
      | Some cond' -> Some (IfZero (cond', t1, t2))
      | None -> None)
  | IfEmpty (List [], t1, _) -> Some t1
  | IfEmpty (List _, _, t2) -> Some t2
  | IfEmpty (cond, t1, t2) -> (
      match ltr_cbv_step cond with
      | Some cond' -> Some (IfEmpty (cond', t1, t2))
      | None -> None)
  (* Cas du point fixe *)
  | Fix (Abs (f, body)) -> let body' = substitution f (Fix (Abs (f, body))) body in
      Some body'
  | Fix f -> (
      match ltr_cbv_step f with
      | Some f' -> Some (Fix f')
      | _ -> failwith "Fix is not an abstraction")
    (* Réduction des termes let *)
  | Let (x, e1, e2) when is_value e1 ->
      (* Remplacer `x` par `e1` dans `e2` *)
      Some (substitution x e1 e2)
  | Let (x, e1, e2) -> (
      (* Réduire `e1` si ce n'est pas une valeur *)
      match ltr_cbv_step e1 with
      | Some e1' -> Some (Let (x, e1', e2))
      | None -> None)
  (* Aucun autre cas ne s'applique *)
  | _ -> None

(* Détermine si un terme est une valeur *)
and is_value (t : pterm) : bool =
  match t with
  | Abs (_, _) -> true
  | Int _ -> true
  | List _ -> true
  | _ -> false


(* Normalise un terme en appliquant ltr_cbv_step jusqu'à ce qu'il ne soit plus possible *)
let rec ltr_cbv_norm (t : pterm) : pterm =
  match ltr_cbv_step t with Some t' -> ltr_cbv_norm t' | None -> t

(* Exception levée quand le temps d'exécution dépasse le timeout *)
exception Timeout

(* Version avec timeout de la normalisation *)
let ltr_cbv_norm_timeout (t : pterm) (timeout : float) : pterm =
  let rec loop t start_time =
    (* Vérifie si le temps écoulé dépasse le timeout *)
    if Sys.time () -. start_time > timeout then raise Timeout
    else match ltr_cbv_step t with Some t' -> loop t' start_time | None -> t
  in
  loop t (Sys.time ())
