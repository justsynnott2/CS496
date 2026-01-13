(* Justin Synnott & Collin Shen *)
open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | Cons(e1,e2) -> 
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>=
    list_of_listVal >>= fun l ->
    return (ListVal(ev1 :: l))
  | Hd(e) ->
    eval_expr e >>=
    list_of_listVal >>= fun l ->
    (match l with
    | h::_ -> return  h)
  | Tl(e) -> 
    eval_expr e >>=
    list_of_listVal >>= fun l ->
    (match l with
    | _::t -> return (ListVal t))
  | IsEmpty(e) ->
    eval_expr e >>=
    list_of_listVal >>= fun l ->
    return (BoolVal (l = []))
  | EmptyList(_t) ->
    return (ListVal [])
  | Tuple es ->
    eval_exprs es >>= fun vs ->
    return (TupleVal vs)
  | Untuple (ids, e1, e2) ->
    eval_expr e1 >>=
    tuple_of_tupleVal >>= fun vs ->
    if List.length ids = List.length vs then
      extend_env_list ids vs >>+ eval_expr e2
    else
      error "Arguments do not match parameters!"

and eval_exprs : expr list -> exp_val list ea_result =
  fun es ->
    match es with
    | [] -> return []
    | h :: t ->
      eval_expr h >>= fun v ->
      eval_exprs t >>= fun vs ->
      return (v :: vs)

(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e


(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
  


