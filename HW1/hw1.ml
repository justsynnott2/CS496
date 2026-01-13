(* Justin Synnott *)
(* ******************************************** *)
(** Basic functions on finite automata *)
(* ******************************************** *)
(**
   Code stub for assignment 1
*)

type symbol = char
type input = char list

type state = string

(* transition function *)
type tf = (state * symbol * state) list

(* initial state * transition function * end state *)
type fa = { states: state list; start:state; tf: tf; final: state list}


(* ******************************************** *)
(* Examples of automata *)
(* ******************************************** *)

let a = {states = ["q0";"q1";"q2"];
         start = "q0";
         tf = [("q0",'a',"q1"); ("q1",'b',"q1"); ("q1",'c',"q2")];
         final = ["q2"]}

let a2 = {states = ["q0";"q1";"q2";"q3";"q4"];
          start = "q0";
          tf = [("q0",'a',"q1"); ("q1",'b',"q1")
               ; ("q1",'c',"q2");  ("q3",'a',"q4")];
          final = ["q2"]
         }

let tf_of_a = [("q0",'a',"q1"); ("q1",'b',"q1"); ("q1",'c',"q2")]

(* ******************************************** *)
(* Helper functions *)
(* ******************************************** *)

let input_of_string s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(* Given a symbol and a transition function return the states connected to that symbol in the form of a list *)
let rec symbol_to_state tf sym =
  match tf with
  | [] -> []
  | (st1,sym1,st2)::t ->
  if sym1 = sym then st1 :: st2 :: []
  else symbol_to_state t sym

(* Removes duplicate elements from a list *)
let rec remove_dups l =
  match l with
  | [] -> []
  | h::t ->
  if List.mem h t then remove_dups t
  else h :: remove_dups t

(* Removes elements from tf list by checking if the states in a transition exist in the states that can be reached *)
let rec remove_tf f sl =
  match f with
  | [] -> []
  | (st1,sym,st2)::t -> 
  if (List.mem st1 sl) && (List.mem st2 sl) then (st1,sym,st2) :: remove_tf t sl
  else remove_tf t sl

(* ******************************************** *)
(* Simulating automata *)
(* ******************************************** *)

let rec apply_transition_function f st sym =
  match f with
  | [] -> None
  | ((st1:state),(sym1:symbol),(st2:state))::t -> 
  if st1 = st && sym1 = sym then Some st2
  else apply_transition_function t st sym

let accept fa input =
  if (List.length input < 2) then false

  (* Checks that first is start and last is final *)
  else if (List.length input = 2) then
  List.mem fa.start (symbol_to_state fa.tf (List.hd input)) &&
  List.fold_left (||) false @@ (List.map (fun sts -> List.mem sts fa.final) (symbol_to_state fa.tf (List.hd (List.rev input))))

  (* Checks front, middle, and last*)
  else
  List.mem fa.start (symbol_to_state fa.tf (List.hd input)) &&
  List.fold_left (&&) true @@ (List.map (fun l -> (List.nth l 0) = (List.nth l 1)) @@ (List.map (fun l -> symbol_to_state fa.tf l) (List.tl (List.rev (List.tl input))))) &&
  List.fold_left (||) false @@ (List.map (fun sts -> List.mem sts fa.final) (symbol_to_state fa.tf (List.hd (List.rev input))))


let rec next f st sym =
  match f with
  | [] -> []
  | ((st1:state),(sym1:symbol),(st2:state))::t -> 
  if st1 = st && sym1 = sym then st2 :: next t st sym
  else next t st sym

let is_deterministic fa =
  let rec deterministic' f =
    match f with
    | [] -> true
    | (st1,sym1,st2)::t ->
    if (List.length (next f st1 sym1)) > 1 then false
    else deterministic' t
  in deterministic' fa.tf

let valid fa =
  (List.length fa.states) = (List.length (remove_dups fa.states))  &&
  List.mem fa.start fa.states &&
  List.fold_left (&&) true @@ (List.map (fun fl -> List.mem fl fa.states) fa.final) &&
  is_deterministic fa

let reachable fa =
  let rec reachable' l1 l2 =
  match l1 with
  | [] -> l2
  | (st1,sym,st2)::t ->
  if List.mem st1 l2 then reachable' t (st2 :: l2)
  else reachable' t l2
in List.rev (remove_dups (reachable' fa.tf [fa.start]))

let non_empty fa =
  List.fold_left (||) false @@ (List.map (fun fl -> List.mem fl (reachable fa)) fa.final)

let remove_dead_states fa =
  {fa with states = (reachable fa);
  tf = (remove_tf fa.tf (reachable fa));
  final = List.filter (fun fl -> List.mem fl (reachable fa)) fa.final
  }
