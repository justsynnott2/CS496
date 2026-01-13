open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  (*| Record ([]) ->
  error "record: no fields"
  | Record (fs) ->
    let (ids, bls) = List.split fs 
    in let (_bls, exp) = List.split bls
    in if List.length (List.sort_uniq compare ids) = List.length ids
    then chk_exprs es >>= fun lt ->
    return (RecordType (List.combine ids lt))
    else error "record: duplicate fields"
  | Proj(e, id) ->
    chk_expr e >>= fun reco ->
    (match te with
      | RecordType fs -> 
        (match List.assoc_opt id reco with
        | Some t -> return t
        return type
        | None -> error "field does not exist"
      | _ -> error "Not a record")
      )
    else error "e must be of record type"*)
  | NewRef(e) -> 
    chk_expr e >>= fun t ->
    return (RefType t)
  | DeRef(e) -> 
    chk_expr e >>= fun r ->
    (match r with
      | RefType t -> return t
      | _ -> error "Not a RefVal")
  | SetRef(e1,e2) -> 
    chk_expr e1 >>= fun t1 ->
    (match t1 with
      | RefType _ -> chk_expr e2 >>= fun _ ->
      return UnitType
      | _ -> error "setref: Expected a reference type")
  | BeginEnd([]) -> return UnitType
  | BeginEnd(es) -> 
    let rec begin_end_helper = function
      | [] -> return UnitType
      | [e] -> chk_expr e >>= fun t ->
      return t
      | e::tl -> chk_expr e >>= fun _ ->
      begin_end_helper tl
    in begin_end_helper es
  | EmptyList(t) -> 
    (match t with
      | Some t' -> return (ListType t')
      | None -> error "emptylist: invalid type")
  | Cons(e1,e2) -> 
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    (match t2 with
      | (ListType t) -> if t1=t
      then return (ListType t)
      else error "cons: type of head and tail do not match"
      | _ -> error "cons: second arguement not a list type")
  | IsEmpty(e) ->
    chk_expr e >>= fun t ->
    (match t with
      | (ListType _) | (TreeType _) -> return BoolType
      | _ -> error "empty?: expected a list type")
  | Hd(e) -> 
    chk_expr e >>= fun t ->
    (match t with 
      | (ListType t') -> return t'
      | _ -> error "hd: expected a list type")
  | Tl(e) -> 
    chk_expr e >>= fun t ->
    (match t with 
      | (ListType t') -> return (ListType t')
      | _ -> error "hd: expected a list type")
  | EmptyTree(t) -> 
    (match t with
      | Some t' -> return (TreeType t')
      | _ -> error "emptytree: invalid type")
  | Node(de,le,re) -> 
    chk_expr de >>= fun tn ->
    chk_expr le >>= fun tl ->
    (match tl with
      | (TreeType t1) -> if t1=tn
      then chk_expr re >>= fun tr ->
      (match tr with
        | (TreeType t2) -> if t2=tn
        then return (TreeType tn)
        else error "node: type of de and re do not match"
        | _ -> error "node: re expected to be a tree type")
      else error "node: type of de and le do not match"
      | _ -> error "node: le expected to be a tree type")
  | CaseT(target,emptycase,id1,id2,id3,nodecase) ->  
  chk_expr target >>= fun trg ->
    (match trg with
      | TreeType t -> 
        chk_expr emptycase >>= fun et ->
        chk_expr nodecase >>= fun nt ->
        if et = nt then
          extend_tenv id1 (TreeType t) >>+
          extend_tenv id2 (TreeType t) >>+
          extend_tenv id3 (TreeType t) >>+
          return nt
        else error "caseT: type of emptycase and nodecase do not match"
      | _ -> error "caseT: target expected to be a tree type")
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)



