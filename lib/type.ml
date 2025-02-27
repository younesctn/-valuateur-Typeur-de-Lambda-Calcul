type pterm =
  | Var of string
  | App of pterm * pterm
  | Abs of string * pterm

let rec print_term (t : pterm) : string =
  match t with
  | Var x -> x
  | App (t1, t2) -> "(" ^ print_term t1 ^ " " ^ print_term t2 ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ print_term t ^ ")"

type ptype = 
  | Vart of string (* Type variable *)
  | Arr of ptype * ptype  (* T1 -> T2 *)
  | Nat (* Type Nat *)

let rec print_type (t : ptype) : string = 
  match t with
  | Vart x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^ " -> " ^ (print_type t2) ^ ")"
  | Nat -> "Nat"

type equa = (ptype * ptype) list (* Liste de contraintes *)
type env = (string * ptype) list (* Environnement associant noms et types *)

let compteur_var_t = ref 0
let nouvelle_var_t () =
    compteur_var_t := !compteur_var_t + 1;
    "T" ^ string_of_int !compteur_var_t

let rec cherche_type (v : string) (e : env) : ptype =
    match e with
    | [] -> failwith ("Variable non trouvée : " ^ v)
    | (x, t) :: rest -> if x = v then t else cherche_type v rest

let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
    match te with
    | Var v -> [(cherche_type v e, ty)]
    | Abs (x, t) ->
        let ta = try cherche_type x e with _ -> Vart (nouvelle_var_t ()) in
        let tr = Vart (nouvelle_var_t ()) in
        let eq = genere_equa t tr ((x, ta) :: e) in
        eq @ [(Arr (ta, tr), ty)]
    | App (t1, t2) ->
        let ta = Vart (nouvelle_var_t ()) in
        (genere_equa t1 (Arr (ta, ty)) e) @ (genere_equa t2 ta e)

let rec occur_check (x : string) (t : ptype) : bool =
    match t with
    | Vart y -> x = y
    | Arr (t1, t2) -> (occur_check x t1) || (occur_check x t2)
    | Nat -> false

exception UnificationFailed of string

(* Substitue une variable dans un type *)
let rec substitue (x : string) (t_sub : ptype) (t : ptype) : ptype =
  match t with
  | Vart y -> if y = x then t_sub else t
  | Arr (t1, t2) -> Arr (substitue x t_sub t1, substitue x t_sub t2)
  | Nat -> t

(* Substitue une variable dans un système d'équations *)
let substitue_dans_systeme (x : string) (t_sub : ptype) (eqs : equa) : equa =
  List.map (fun (t1, t2) -> (substitue x t_sub t1, substitue x t_sub t2)) eqs

let rec apply_subst (eqs : equa) (t : ptype) : ptype =
  match eqs with
  | [] -> t
  | (Vart x, t_sub) :: rest -> apply_subst rest (substitue x t_sub t)
  | _ -> (
    match t with
    | Arr (t1, t2) -> Arr (apply_subst eqs t1, apply_subst eqs t2)
    | Vart v -> (
      try let (_, t_sub) = List.find (function (Vart x, _) when x = v -> true | _ -> false) eqs in t_sub
      with Not_found -> t
      )
    | _ -> t
    )

(* Une étape d'unification*)
let rec unification_step (eqs : equa) (subs : equa) : equa =
  match eqs with
  | [] -> subs
  | (t1, t2) :: rest -> 
    let t1' = apply_subst subs t1 in
    let t2' = apply_subst subs t2 in
    if t1' = t2' then unification_step rest subs
    else (
      match (t1', t2') with
      | (Vart x, _) -> if occur_check x t2' then failwith ("Échec de l'unification : " ^ x ^ " occurs in " ^ print_type t2') else unification_step (substitue_dans_systeme x t2' rest) ((Vart x, t2') :: subs)
      | (_, Vart x) -> if occur_check x t1' then failwith ("Échec de l'unification : " ^ x ^ " occurs in " ^ print_type t1') else unification_step (substitue_dans_systeme x t1' rest) ((Vart x, t1') :: subs)
      | (Arr (t1, t2), Arr (t1', t2')) -> unification_step ((t1, t1') :: (t2, t2') :: rest) subs
      | _ -> failwith ("Échec de l'unification : " ^ print_type t1' ^ " != " ^ print_type t2')
    )

let unification (eqs : equa) : equa option =
  try Some (unification_step eqs []) with _ -> None

let find_type (eqs : equa) (t : ptype) : ptype =
  match t with
  | Vart _ -> (
    try List.find (fun (_,t') -> t' = t) eqs |> fst
    with Not_found -> t
    )
  | _ -> t

(* Infère le type d'un terme avec un environnement donné, renvoie un ptype *)
let infere_type_no_timeout (term : pterm) (env : env) : ptype =
  let t = Vart (nouvelle_var_t ()) in
  let eqs = genere_equa term t env in
  let eqs' = unification eqs in
  match eqs' with
  | None -> failwith "Échec de l'unification"
  | Some e -> 
    let ft = apply_subst e t in
    find_type e ft


(*l'ajout du timeout a été effectué avec l'aide d'une IA*)
exception TypeInferenceTimeout of string

let unifie_avec_timeout (eqs : equa) (timeout : float) : equa =
  let start_time = Sys.time () in
  let rec unification_with_timeout eqs subs =
    if Sys.time () -. start_time > timeout then
      raise (TypeInferenceTimeout "Timeout dépassé lors de l'unification")
    else
      match eqs with
      | [] -> subs
      | (t1, t2) :: rest ->
          let t1' = apply_subst subs t1 in
          let t2' = apply_subst subs t2 in
          if t1' = t2' then
            unification_with_timeout rest subs
          else
            match (t1', t2') with
            | (Vart x, _) ->
                if occur_check x t2' then
                  failwith ("Échec de l'unification : " ^ x ^ " occurs in " ^ print_type t2')
                else
                  let updated_eqs = substitue_dans_systeme x t2' rest in
                  let updated_subs = (Vart x, t2') :: subs in
                  unification_with_timeout updated_eqs updated_subs
            | (_, Vart x) ->
                if occur_check x t1' then
                  failwith ("Échec de l'unification : " ^ x ^ " occurs in " ^ print_type t1')
                else
                  let updated_eqs = substitue_dans_systeme x t1' rest in
                  let updated_subs = (Vart x, t1') :: subs in
                  unification_with_timeout updated_eqs updated_subs
            | (Arr (t1, t2), Arr (t1', t2')) ->
                unification_with_timeout ((t1, t1') :: (t2, t2') :: rest) subs
            | _ ->
                failwith ("Échec de l'unification : " ^ print_type t1' ^ " != " ^ print_type t2')
  in
  unification_with_timeout eqs []

(* Infère le type d'un terme avec un environnement donné, avec un timeout *)
let infere_type (term : pterm) (env : env) (timeout : float) : ptype =
  let t = Vart (nouvelle_var_t ()) in
  let eqs = genere_equa term t env in
  let eqs' =
    try unifie_avec_timeout eqs timeout
    with TypeInferenceTimeout msg -> raise (TypeInferenceTimeout msg)
  in
  let ft = apply_subst eqs' t in
  find_type eqs' ft

