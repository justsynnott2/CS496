(* Justin Synnott *)
(* I pledge my honor that I have abided by the Stevens Honor System *)

type dTree =
| Leaf of int
| Node of char * dTree * dTree

let tLeft = Node('w',
                Node('x',Leaf 2,Leaf 5),
                Leaf 8)

let tRight = Node('w',
                Node('x',Leaf 2,Leaf 5),
                Node('y',Leaf 7,Leaf 5))

let f1 = [([0;0;0] , 0);
([0;0;1] , 1);
([0;1;0] , 1);
([0;1;1] , 0);
([1;0;0] , 1);
([1;0;1] , 0);
([1;1;0] , 0);
([1;1;1] , 1)]

let f2 = (['x';'y';'z'],[([0;0;0] , 0);
([0;0;1] , 1);
([0;1;0] , 1);
([0;1;1] , 0);
([1;0;0] , 1);
([1;0;1] , 0);
([1;1;0] , 0);
([1;1;1] , 1)])
                

let rec height t = 
    match t with
    | Leaf n -> 1
    | Node(c,lt,rt) -> max (height lt + 1) (height rt + 1)

let rec size t =
    match t with
    | Leaf n -> 1
    | Node(c,lt,rt) -> 1 + size lt + size rt

let rec paths t =
    let rec paths_helper tr l =
        match tr with
        | Leaf n -> [[]]
        | Node(d,lt,rt) ->
        let left = paths_helper lt l in
        let right = paths_helper rt l in
        List.map (fun l2 -> 0 :: l2) left @ List.map (fun l2 -> 1 :: l2) right in
    paths_helper t []

let is_perfect t =
    let rec is_perfect_helper paths len =
        match paths with
        | [] -> true
        | h::t ->
        if (List.length h) = len then is_perfect_helper t len
        else false
    in is_perfect_helper (List.tl (paths t)) (List.length (List.hd (paths t)))

let rec map f g t =
    match t with
    | Leaf n -> Leaf (g n)
    | Node(c,lt,rt) -> Node((f c),(map f g lt),(map f g rt))

let rec list_to_tree l =
    match l with
    | [] -> Leaf 0
    | h::t -> Node(h,(list_to_tree t),(list_to_tree t))

let rec replace_leaf_at t f =
    match f with
    | [] -> t
    | (l,v)::tl -> 
    let rec replace_leaf_at_helper list tree value =
        match tree with
        | Leaf n -> Leaf value
        | Node(d,lt,rt) -> 
        if (List.hd list) = 0 then Node(d,replace_leaf_at_helper (List.tl list) lt value,rt)
        else Node(d,lt,replace_leaf_at_helper (List.tl list) rt value)
    in replace_leaf_at (replace_leaf_at_helper l t v) tl

let rec bf_to_dTree f =
    let t = list_to_tree (fst f) in
    replace_leaf_at t (snd f)
