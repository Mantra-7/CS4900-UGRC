open Prims
let rec sorted : 'a . ('a -> 'a -> Prims.bool) -> 'a Prims.list -> Prims.bool
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | x::y::xs -> (f x y) && (sorted f (y :: xs))
      | uu___1 -> true
type 'a total_order = 'a -> 'a -> Prims.bool
let rec count : 'a . 'a -> 'a Prims.list -> Prims.nat =
  fun x ->
    fun uu___ ->
      match uu___ with
      | hd::tl ->
          (if hd = x then Prims.int_one else Prims.int_zero) + (count x tl)
      | [] -> Prims.int_zero
let rec partition :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> ('a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> ([], [])
      | hd::tl ->
          let uu___1 = partition f tl in
          (match uu___1 with
           | (l1, l2) -> if f hd then ((hd :: l1), l2) else (l1, (hd :: l2)))
type ('a, 'l, 'm) is_permutation = unit
let rec quicksort : 'a . 'a total_order -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | pivot::tl ->
          let uu___ = partition (f pivot) tl in
          (match uu___ with
           | (hi, lo) ->
               let m =
                 FStar_List_Tot_Base.op_At (quicksort f lo) (pivot ::
                   (quicksort f hi)) in
               m)