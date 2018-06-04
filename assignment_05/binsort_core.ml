type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type sumbool =
| Left
| Right

(** val le_lt_dec : int -> int -> sumbool **)

let rec le_lt_dec n m =
  (fun zero succ n ->
    if n=0 then zero () else succ (n-1))
    (fun _ ->
    Left)
    (fun n0 ->
    (fun zero succ n ->
    if n=0 then zero () else succ (n-1))
      (fun _ ->
      Right)
      (fun m0 ->
      le_lt_dec n0 m0)
      m)
    n

(** val le_gt_dec : int -> int -> sumbool **)

let le_gt_dec n m =
  le_lt_dec n m

(** val le_dec : int -> int -> sumbool **)

let le_dec n m =
  le_gt_dec n m

type bintree =
| Leaf
| Branch of int * bintree * bintree

(** val insert : int -> bintree -> bintree **)

let rec insert x = function
| Leaf -> Branch (x, Leaf, Leaf)
| Branch (y, l, r) ->
  (match le_dec x y with
   | Left -> Branch (y, (insert x l), r)
   | Right -> Branch (y, l, (insert x r)))

(** val list2bin : int list -> bintree **)

let rec list2bin = function
| Nil -> Leaf
| Cons (x, xs) -> insert x (list2bin xs)

(** val inorder : bintree -> int list **)

let rec inorder = function
| Leaf -> Nil
| Branch (x, l, r) -> app (inorder l) (Cons (x, (inorder r)))

(** val binsort : int list -> int list **)

let binsort l =
  inorder (list2bin l)
