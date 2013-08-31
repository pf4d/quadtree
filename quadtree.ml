(*
    CSCI 332 Algorithms
    Spring 2013
    Project 1
    Evan Cummings
*)

type 'a quadtree =
    | Empty     of int
    | Singleton of int * int * int * 'a
    | Quad      of int * 'a quadtree * 'a quadtree * 'a quadtree * 'a quadtree


(* function to insert a value 'v' into a quadtree 'qt' 
   at (x,y) location 'coord'  *)

let rec insert qt coord v = 
  let x = fst(coord) and y = snd(coord) in
  match qt with
  | Empty(n)              -> Singleton(n, x, y, v)
  | Singleton(n,xs,ys,vs) -> let m = n/2 in
      insert (insert (Quad(n, (Empty m), (Empty m), (Empty m), (Empty m))) 
          (xs, ys) vs) (x,y)  v
  | Quad(n,nw,ne,sw,se)   -> let m = n/2 in 
      match (x < m, y < m) with
      | (true,  true)  -> Quad(n, (insert nw (x,y) v), ne, sw, se)
      | (true,  false) -> Quad(n, nw, ne, (insert sw (x,(y-m)) v), se)
      | (false, true)  -> Quad(n, nw, (insert ne ((x-m),y) v), sw, se)
      | (false, false) -> Quad(n, nw, ne, sw, (insert se ((x-m),(y-m)) v))


(* creates a quadtree size 'n' with values inserted from the list of 
   (x,y,v) tuples - 'x','y' coordinates and 'v' the value *)

let makeqt n lst =
  let rec helper n lst qt =
    match lst with
      | x::xs ->
        (
          match x with
          | (x1,x2,x3) -> helper n xs (insert qt (x1,x2) x3)
        )
      | []    -> qt
    and m = n/2
  in
    helper n lst (Quad(n, (Empty m), (Empty m), (Empty m), (Empty m)))


(* function provides a list of (x,y,v) tuples within a box with Northwest 
   corner (ax,ay) and Southeast corner (bx,by) *)

let range qt (ax,ay) (bx,by) = 
  (* the qt global coord = (ux,uy) *)
  let rec recurse qt (ax,ay) (bx,by) (ux, uy) =
    match qt with
    | Empty(n)              -> []
    | Singleton(n,xs,ys,vs) -> 
      ( let x = xs + ux and y = ys + uy in
        match (x >= ax, y >= ay, x <= bx, y <= by) with
        | (true,  true,  true,  true)  -> [(x, y, vs)]
        | _                            -> []
      )
    | Quad(n,nw,ne,sw,se)   -> 
        let m = n/2 and test x y = (ax < ux+x && ay < uy+y) in
        (if test m m then recurse nw (ax, ay) (bx, by) (ux,   uy)   else []) @
        (if test n m then recurse ne (ax, ay) (bx, by) (ux+m, uy)   else []) @
        (if test m n then recurse sw (ax, ay) (bx, by) (ux,   uy+m) else []) @
        (if test n n then recurse se (ax, ay) (bx, by) (ux+m, uy+m) else []) 
  in
    recurse qt (ax,ay) (bx,by) (0,0)


(* rotate all the elements of a quadtree 90 degrees counter-clockwise *)

let rec rotate qt = 
  match qt with
  | Quad(n,nw,ne,sw,se) -> 
      Quad(n,(rotate ne),(rotate se),(rotate nw),(rotate sw))
  | Empty(n)            -> Empty(n)
  | Singleton(n,x,y,v)  -> 
      let m = n/2 and k = n-1 in
      match (x < m, y < m) with
      | (true,  true)  -> Singleton(n, x,   k-y, v)
      | (true,  false) -> Singleton(n, k-x, y,   v)
      | (false, true)  -> Singleton(n, x-k, y,   v)
      | (false, false) -> Singleton(n, x,   y-k, v)


(* mirror all elements in 'qt' across the x-axis *)

let rec mirrorNS qt = 
  match qt with
  | Quad(n,nw,ne,sw,se) -> 
      Quad(n, (mirrorNS sw), (mirrorNS se), (mirrorNS nw), (mirrorNS ne))
  | Empty(n)            -> Empty(n)
  | Singleton(n,x,y,v)  -> 
      let m = n/2 and k = n-1 in 
      match y < m with
      | true  -> Singleton(n, x, k-y, v)
      | false -> Singleton(n, x, y-k, v)


(* mirror all elements in 'qt' across the y-axis *)

let rec mirrorEW qt =
  match qt with
  | Quad(n,nw,ne,sw,se) -> 
      Quad(n, (mirrorEW ne), (mirrorEW nw), (mirrorEW se), (mirrorEW sw))
  | Empty(n)            -> Empty(n)
  | Singleton(n,x,y,v)  -> 
      let m = n/2 and k = n-1 in 
      match x < m with
      | true  -> Singleton(n, k-x, y, v)
      | false -> Singleton(n, x-k, y, v)


(* function which applies the function 'f' to every value in 'qt' *)

let mapqt f qt =
  let rec recurse qt = 
    match qt with
    | Empty(n)            -> Empty(n)
    | Singleton(n,x,y,v)  -> Singleton(n,x,y,(f v))
    | Quad(n,nw,ne,sw,se) -> 
        Quad(n, (recurse nw), (recurse ne), (recurse sw), (recurse se))
  in
    recurse qt


(* convenience function to print a string quadtree, where
   each data item is a single character, and empty positions
   are printed as a dot *)

let printq q =
  let rec zipconcat lst1 lst2 = match (lst1, lst2) with
      | (x::xs, y::ys) -> (x ^ y) :: zipconcat xs ys
      | _              -> []
    and repeat n x     = if n < 1 then [] else x :: repeat (n-1) x
    and dots n         = if n < 1 then "" else "." ^ (dots (n-1))
    and toStringList q = match q with
      | Empty(n)            -> repeat n (dots n)
      | Singleton(n,x,y,v)  -> 
          (repeat y (dots n))
          @ [ (dots x) ^ v ^ (dots (n-x-1)) ]
          @ (repeat (n-y-1) (dots n))
      | Quad(n,nw,ne,sw,se) -> 
          (zipconcat (toStringList nw) (toStringList ne))
          @ (zipconcat (toStringList sw) (toStringList se))
    and toString q =
      List.fold_left (^) "" (List.map (fun x -> x ^ "\n") (toStringList q))
  in
    print_string (toString q)


(* a smiley face (will raise an exception until makeqt is implemented): *)

let smiley = makeqt 16 (List.map (fun (x,y) -> (x,y,"#")) [
    (4,2);(4,3);(5,2);(5,3);
    (9,3);(10,3);(11,3);(12,3);
    (2,6);(2,7);(3,8);(4,9);(5,9);(6,10);(7,10);
    (8,10);(9,10);(10,9);(11,9);(12,8);(13,7);(13,6)
]);;


(* testing of each method *)

let q        = makeqt 16 [(9,5,"A"); (10,6,"B")];;
let fifify x = "F";;

range q (0,0) (15,15)  ;;
range q (3,4) (9,9)    ;;
range q (10,1) (15,15) ;;
range q (11,1) (15,15) ;;

printq smiley;;
printq (rotate smiley);;
printq (mirrorNS smiley);;
printq (mirrorEW smiley);;
printq (mapqt fifify smiley);;
