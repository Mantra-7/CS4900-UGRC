module Interval_tree

open FStar.List.Tot
open QuickSort.List
open Interval

type interval_tree_aux =
  | Empty : interval_tree_aux
  | Node : (mid:nat) -> (l:list interval) -> (r:list interval{is_permutation interval l r}) -> (left:interval_tree_aux) -> (right:interval_tree_aux) -> interval_tree_aux

(* Returns true if interval i is in the tree it *)
let rec in_itv_tree (i:interval) (it:interval_tree_aux) : Tot bool =
  match it with
  | Empty -> false
  | Node m l r left right -> (mem i l) || (in_itv_tree i left) || (in_itv_tree i right)

(* Returns number of times interval i is in the tree it *)
let rec count_itv_tree (i:interval) (it:interval_tree_aux) : Tot nat =
  match it with
  | Empty -> 0
  | Node m l r left right -> (count i l) + (count_itv_tree i left) + (count_itv_tree i right)

let rec to_itvs (it:interval_tree_aux) : Tot (itvs:list interval{forall i. ((count i itvs) = (count_itv_tree i it)) /\ ((mem i itvs) <==> (in_itv_tree i it))})=
    match it with
    | Empty -> []
    | Node _ l r left right ->
           let ll = to_itvs left in
           let rr = to_itvs right in
           l@(ll@rr)

let rec check_list (#a:eqtype) (l:list a) (f:a->bool) : Tot (b:bool{b <==> (forall e. ((mem e l) ==> f e))}) =
  match l with
    | [] -> true
    | hd::tl -> (f hd) && (check_list tl f)

(* func_left sorts in increasing order based on left bound first and then rbound *)
let func_left : total_order interval =
  let f (i1 i2:interval) = if i1.lbound < i2.lbound then true else if i1.lbound > i2.lbound then false
           else i1.rbound <= i2.rbound in
  f

(* func_right sorts in decreasing order based on right bound first and then lbound *)
let func_right : total_order interval =
  let f (i1 i2:interval) = if i1.rbound > i2.rbound then true else if i1.rbound < i2.rbound then false
           else i1.lbound >= i2.lbound in
  f

let rec remove (#a:eqtype) (x:a) (l:list a{mem x l})
  : Tot (l1:list a{(forall e. (x <> e) ==> (count e l = count e l1)) /\ (count x l = count x l1 + 1) /\ (length l1 = length l - 1)}) =
  match l with
  |[] -> []
  |hd::tl -> if x = hd then tl else hd::remove x tl

let non_empty_impl_mem (#a:eqtype) (l:list a) : Lemma (ensures ((length l > 0) ==> (exists e. (mem e l)))) =
  match l with
  | hd::tl -> ()
  | [] -> ()

let no_mem_impl_empty (#a:eqtype) (l:list a) : Lemma (ensures (forall e. not (mem e l)) ==> length l = 0) =
  non_empty_impl_mem l;
  ()

let rec same_length (#a:eqtype) (l:list a) (m:list a) : Lemma (requires is_permutation a l m) (ensures length l = length m) =
  match l with
  |[] -> no_mem_impl_empty m;
        ()
  |hd::tl -> same_length tl (remove hd m)

let rec compute_bounds (itvs:list interval) : (l:list nat{((length l) % 2 = 0) /\ (forall b. mem b l <==> (exists i. mem i itvs /\ (b = i.lbound \/ b = i.rbound)))}) =
  match itvs with
  | [] -> []
  | hd::tl -> (hd.lbound::(hd.rbound::(compute_bounds tl)))

let median_helper (l:list nat{sorted (fun (x y:nat) -> x <= y) l /\ length l > 0}) : (i:nat{((length l % 2 = 0) ==> (i = (length l / 2))) /\ ((length l % 2 = 1) ==> (i = ((length l -1 ) / 2)))}) =
  let n = length l in
  if n % 2 = 1 then
    (n-1) / 2
  else
    n / 2

let rec my_ind (#a:eqtype) (l:list a) (i:nat{i < length l}) : Tot (e:a{mem e l /\ count e l > 0}) =
  match l with
  | h::t -> if i = 0 then h else my_ind t (i-1)

let median_bounds (itvs:list interval{length itvs > 0}) : (m:nat{exists i. mem i itvs /\ contains m i}) =
  let bounds = compute_bounds itvs in
  let sorted_bounds = quicksort (fun (x y:nat) -> x <= y) bounds in
  same_length bounds sorted_bounds;
  let mid_ind = median_helper sorted_bounds in
  let mid = my_ind sorted_bounds mid_ind in
  assert(exists i. (mem i itvs) /\ ((mid = i.lbound) \/ (mid = i.rbound)));
  mid

let rec ordered (it:interval_tree_aux) =
  match it with
  | Empty -> true
  | Node mid l r left right -> (length l > 0) &&
                            (check_list (to_itvs left) (is_before mid)) &&
                            (check_list (to_itvs right) (is_after mid)) &&
                            (check_list l (contains mid)) &&
                            (sorted func_left l) &&
                            (sorted func_right r) &&
                            (mid = (median_bounds (to_itvs it))) &&
                            (ordered left) &&
                            (ordered right)

type interval_tree = (it:interval_tree_aux{ordered it})

let partition_upd (itvs:list interval{length itvs > 0}) (f1:interval->bool) (f2:interval->bool) : (left:list interval{forall l. (mem l left) ==> (f1 l)}) * (mid:list interval{(forall m. (mem m mid ==> ((f1 m) = false) /\ (f2 m) = false))}) * (right:list interval{forall r. (mem r right) ==> (((f1 r) = false) /\ ((f2 r) = true))}) =
  let left_itvs, maybe_right_itvs =
    partition f1 itvs in
  let right_itvs, mid_itvs =
    partition f2 maybe_right_itvs in
  left_itvs, mid_itvs, right_itvs

let rec count_bounds (itvs:list interval) (b:nat) : nat =
  match itvs with
  | [] -> 0
  | hd::tl -> if (hd.lbound = hd.rbound) then
                if hd.lbound = b then 2 + count_bounds tl b
                else count_bounds tl b
            else if (hd.lbound = b) || (hd.rbound = b) then 1 + count_bounds tl b
                 else count_bounds tl b

let cons_lemma (#a:eqtype) (l:list a) (e:a) : Lemma (ensures (forall b. (b <> e) ==> (count b l) = (count b (e::l))) /\ (count e l = count e (e::l) - 1)) =
  ()

let get_hd (#a:eqtype) (l:list a{length l >0}) : a =
  match l with
  | hd::_ -> hd

let get_tl (#a:eqtype) (l:list a{length l >0}) : (list a) =
  match l with
  | _::tl -> tl

let cons_count_lemma_1 (hd:interval) (tl:list interval) : Lemma (requires hd.rbound = hd.lbound) (ensures (count_bounds (hd::tl) hd.rbound = count_bounds tl hd.rbound + 2)) =
  ()

let cons_count_lemma_2 (hd:interval) (tl:list interval) : Lemma (requires hd.rbound <> hd.lbound) (ensures (count_bounds (hd::tl) hd.rbound = count_bounds tl hd.rbound + 1) /\ (count_bounds (hd::tl) hd.lbound = count_bounds tl hd.lbound + 1)) =
  ()

let rec bounds_count_lemma (itvs:list interval) : Lemma (ensures (forall b. (count_bounds itvs b) = count b (compute_bounds itvs))) =
  match itvs with
  | [] -> ()
  | hd::tl -> let t = compute_bounds tl in
            bounds_count_lemma tl;
            cons_lemma t hd.rbound;
            cons_lemma (hd.rbound::t) hd.lbound;
            if hd.rbound = hd.lbound then cons_count_lemma_1 hd tl
            else cons_count_lemma_2 hd tl

let rec remove_lemma_1 (itvs:list interval) (i:interval) : Lemma (requires (mem i itvs) /\ i.lbound = i.rbound) (ensures (count_bounds itvs i.lbound = count_bounds (remove i itvs) i.lbound + 2) /\ (forall b. b <> i.lbound ==> (count_bounds itvs b = count_bounds (remove i itvs) b))) =
  match itvs with
  | [] -> ()
  | hd::tl -> if hd = i then cons_count_lemma_1 hd tl
            else
            remove_lemma_1 tl i

let cons_count_diff_lemma (l1 l2:list interval) (i:interval) (e:nat): Lemma (ensures (count_bounds l1 e - count_bounds l2 e) =  (count_bounds (i::l1) e - count_bounds (i::l2) e)) =
  ()

let rec remove_lemma_2 (itvs:list interval) (i:interval) : Lemma (requires (mem i itvs) /\ i.lbound <> i.rbound) (ensures (count_bounds itvs i.lbound = count_bounds (remove i itvs) i.lbound + 1) /\ (count_bounds itvs i.rbound = count_bounds (remove i itvs) i.rbound + 1) /\ (forall b. (b <> i.lbound /\ b <> i.rbound) ==> (count_bounds itvs b = count_bounds (remove i itvs) b))) =
  match itvs with
  | [] -> ()
  | hd::tl -> if hd = i then cons_count_lemma_2 hd tl
              else
                begin
                  remove_lemma_2 tl i;
                  assert(count_bounds tl i.lbound = count_bounds (remove i tl) i.lbound + 1);
                  cons_count_diff_lemma tl (remove i tl) hd i.lbound;
                  assert(count_bounds (hd::tl) i.lbound = count_bounds (hd::(remove i tl)) i.lbound + 1);
                  assert(count_bounds itvs i.lbound = count_bounds (remove i itvs) i.lbound + 1)
                end

let rec count_bounds_perm_lemma (l1:list interval) (l2:list interval) : Lemma (requires is_permutation interval l1 l2) (ensures forall b. (count_bounds l1 b) = count_bounds l2 b) =
  same_length l1 l2;
 match l1 with
  | [] -> ()
  | hd::tl -> let rmx = (remove hd l2) in
              count_bounds_perm_lemma tl rmx;
              if hd.lbound = hd.rbound
              then
                begin
                  remove_lemma_1 l2 hd;
                  cons_count_lemma_1 hd tl
                end
              else
                begin
                  remove_lemma_2 l2 hd;
                  cons_count_lemma_2 hd tl
                end

let bound_perm (l1:list interval{length l1 > 0}) (l2:list interval{length l2 > 0}) : Lemma (requires is_permutation interval l1 l2) (ensures is_permutation nat (compute_bounds l1) (compute_bounds l2)) =
  assert(forall i. (count i l1) = count i l2);
  count_bounds_perm_lemma l1 l2;
  assert(forall b. (count_bounds l1 b) = count_bounds l2 b);
  bounds_count_lemma l1;
  bounds_count_lemma l2

let rec mem_impl_geq (#a:eqtype) (l:list a{length l > 0}) (f:total_order a) (e:a) : Lemma (requires sorted f l /\ count e l > 0) (ensures f (get_hd l) e) =
  match l with
  | hd::tl -> if hd = e then ()
            else mem_impl_geq tl f e

let sorted_perm_head_same (l1:list nat{length l1 > 0}) (l2:list nat{length l2 > 0}) : Lemma (requires (is_permutation nat l1 l2) /\ (sorted (fun (x y:nat) -> x <= y) l1) /\ (sorted (fun (x y:nat) -> x <= y) l2)) (ensures get_hd l1 = get_hd l2) =
  let h1 = get_hd l1 in
  let h2 = get_hd l2 in
  mem_impl_geq l1 (fun (x y:nat) -> x <= y) h2;
  mem_impl_geq l2  (fun (x y:nat) -> x <= y) h1

let rec sorted_perm_same (l1:list nat) (l2:list nat) : Lemma (requires (is_permutation nat l1 l2) /\ (sorted (fun (x y:nat) -> x <= y) l1) /\ (sorted (fun (x y:nat) -> x <= y) l2)) (ensures l1 = l2) =
  same_length l1 l2;
  match l1,l2 with
  | [],[] -> ()
  | h1::t1,h2::t2 -> sorted_perm_head_same l1 l2;
                    cons_lemma t1 h1;
                    cons_lemma t2 h2;
                    sorted_perm_same t1 t2

let eq_median (l1:list interval{length l1 > 0}) (l2:list interval{length l2 > 0}) : Lemma (requires is_permutation interval l1 l2) (ensures (median_bounds l1) = (median_bounds l2)) =
  let b1 = (compute_bounds l1) in
  let b2 = (compute_bounds l2) in
  bound_perm l1 l2;
  let sb1 = quicksort (fun (x y:nat) -> x <= y) b1 in
  let sb2 = quicksort (fun (x y:nat) -> x <= y) b2 in
  sorted_perm_same sb1 sb2

let get_left (intervals:list interval{length intervals > 0}) (f1:interval->bool) (f2:interval->bool) : (left:list interval{forall l. (mem l left) ==> (f1 l)}) =
  let p = partition_upd intervals f1 f2 in
  match p with
  | (left,_,_) -> left

let get_mid (intervals:list interval{length intervals > 0}) (f1:interval->bool) (f2:interval->bool) : (mid:list interval{(forall m. (mem m mid ==> ((f1 m) = false) /\ (f2 m) = false))}) =
  let p = partition_upd intervals f1 f2 in
  match p with
  | (_,mid,_) -> mid

let get_right (intervals:list interval{length intervals > 0}) (f1:interval->bool) (f2:interval->bool) : (right:list interval{forall r. (mem r right) ==> (((f1 r) = false) /\ ((f2 r) = true))}) =
  let p = partition_upd intervals f1 f2 in
  match p with
  | (_,_,right) -> right

let partition_is_perm (itvs:list interval{length itvs > 0}) (f1 f2 : interval->bool) : Lemma (ensures is_permutation interval itvs ((get_mid itvs f1 f2)@((get_left itvs f1 f2)@(get_right itvs f1 f2)))) =
  ()

let pairwise_perm_is_perm (l1 l2 l3 m1 m2 m3:list interval) : Lemma (requires (is_permutation interval l1 m1) /\ (is_permutation interval l2 m2) /\ (is_permutation interval l3 m3)) (ensures is_permutation interval (l1@(l2@l3)) (m1@(m2@m3))) =
  ()

let perm_check_eq (l1 l2:list interval) (f:interval->bool) : Lemma (requires check_list l1 f /\ is_permutation interval l1 l2) (ensures check_list l2 f) =
  ()

val create (intervals:list interval) : Tot (it:interval_tree{(is_permutation interval intervals (to_itvs it))}) (decreases %[length intervals])
let rec create intervals =
  match intervals with
  | [] -> Empty
  | intervals ->
    let mid = (median_bounds intervals) in
    let left_list, mid_list, right_list = partition_upd intervals (is_before mid) (is_after mid) in
    let l = quicksort func_left mid_list in
    let r = quicksort func_right mid_list in
    assert(length mid_list > 0);
    same_length mid_list l;
    let left = (create left_list) in
    let right = (create right_list) in
    let l_itvs = (to_itvs left) in
    let r_itvs = (to_itvs right) in
    let it = Node mid l r left right in
    let it_itvs = (to_itvs it) in
    perm_check_eq mid_list l (contains mid);
    perm_check_eq left_list l_itvs (is_before mid);
    perm_check_eq right_list r_itvs (is_after mid);
    partition_is_perm intervals (is_before mid) (is_after mid);
    pairwise_perm_is_perm mid_list left_list right_list l l_itvs r_itvs;
    eq_median intervals it_itvs;
    it

let rec mem_impl_geq_forall (#a:eqtype) (l:list a{length l > 0}) (f:total_order a) : Lemma (requires sorted f l) (ensures forall e. (count e l > 0) ==> f (get_hd l) e) =
  match l with
  | [] -> ()
  | hd::[] -> ()
  | hd::tl -> mem_impl_geq_forall tl f

let rec filter_left (xmid:nat) (l:list interval{sorted func_left l /\ check_list l (contains xmid)}) (qx:nat{qx < xmid}) :  Tot (t:list interval{(forall i. (mem i t) <==> ((mem i l) /\ (contains qx i))) /\ (forall i. (contains qx i) ==> (count i l = count i t))}) =
  match l with
    | [] -> []
    | hd::tl -> if (contains qx hd) then hd::(filter_left xmid tl qx) else
              begin
              //assert(hd.lbound > qx);
              mem_impl_geq_forall l func_left;
              //assert(forall i. (mem i tl) ==> func_left hd i);
              []
              end

let rec filter_right (xmid:nat) (l:list interval{sorted func_right l /\ check_list l (contains xmid)}) (qx:nat{qx >= xmid}) :  Tot (t:list interval{(forall i. (mem i t) <==> ((mem i l) /\ (contains qx i))) /\ (forall i. (contains qx i) ==> (count i l = count i t))}) =
  match l with
    | [] -> []
    | hd::tl -> if (contains qx hd) then hd::(filter_right xmid tl qx) else
              begin
              //assert(hd.rbound < qx);
              mem_impl_geq_forall l func_right;
              //assert(forall i. (mem i tl) ==> func_right hd i);
              []
              end

val query (qx:nat) (it:interval_tree) : Tot (l:list interval{(forall i. (mem i l) <==> ((contains qx i) /\ (in_itv_tree i it))) /\ (forall i. (contains qx i) ==> (count_itv_tree i it = count i l))}) (decreases %[length (to_itvs it)])
let rec query qx it =
    match it with
    | Empty -> []
    | Node mid l r left right ->
      if qx < mid
      then (filter_left mid l qx)@(query qx left)
      else (filter_right mid r qx)@(query qx right)
