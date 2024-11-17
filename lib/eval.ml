(* Définition du type pour représenter les termes du lambda-calcul *)
type pterm =
  (* Une variable est représentée par une chaîne de caractères *)
  | Var of string
  (* Une application est composée de deux termes : le terme fonction et son argument *)
  | App of pterm * pterm
  (* Une abstraction (fonction) avec un paramètre nommé et un corps *)
  | Abs of string * pterm

(* Fonction pour convertir un terme en chaîne de caractères lisible *)
let rec print_term (t : pterm) : string =
  match t with
  | Var x -> x
  | App (t1, t2) -> "(" ^ print_term t1 ^ " " ^ print_term t2 ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ print_term t ^ ")"

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
      (* Cherche si la variable doit être renommée selon l'environnement *)
      match List.assoc_opt x env with Some new_x -> Var new_x | None -> Var x)
  | Abs (x, body) ->
      (* Crée un nouveau nom pour le paramètre et l'ajoute à l'environnement *)
      let new_x = nouvelle_var () in
      let new_env = (x, new_x) :: env in
      Abs (new_x, alphaconv body new_env)
  | App (t1, t2) ->
      (* Applique l'α-conversion récursivement aux deux sous-termes *)
      App (alphaconv t1 env, alphaconv t2 env)

(* Effectue la substitution [x -> n]t : remplace x par n dans t *)
let rec substitution (x : string) (n : pterm) (t : pterm) : pterm =
  match t with
  | Var y ->
      if y = x then n else t (* Remplace la variable si c'est celle cherchée *)
  | App (t1, t2) ->
      App (substitution x n t1, substitution x n t2)
      (* Applique récursivement *)
  | Abs (y, body) ->
      if y = x then Abs (y, body)
        (* Pas de substitution si la variable est liée *)
      else
        Abs (y, substitution x n body) (* Applique récursivement à body *)

(* Effectue une étape de réduction en stratégie call-by-value de gauche à droite *)
let rec ltr_cbv_step (t : pterm) : pterm option =
  match t with
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
  | _ -> None

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
