open Prims
type interval_tree_aux =
  | Empty 
  | Node of Prims.nat * Interval.interval Prims.list * Interval.interval
  Prims.list * interval_tree_aux * interval_tree_aux 
let (uu___is_Empty : interval_tree_aux -> Prims.bool) =
  fun projectee -> match projectee with | Empty -> true | uu___ -> false
let (uu___is_Node : interval_tree_aux -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Node (mid, l, r, left, right) -> true
    | uu___ -> false
let (__proj__Node__item__mid : interval_tree_aux -> Prims.nat) =
  fun projectee ->
    match projectee with | Node (mid, l, r, left, right) -> mid
let (__proj__Node__item__l :
  interval_tree_aux -> Interval.interval Prims.list) =
  fun projectee -> match projectee with | Node (mid, l, r, left, right) -> l
let (__proj__Node__item__r :
  interval_tree_aux -> Interval.interval Prims.list) =
  fun projectee -> match projectee with | Node (mid, l, r, left, right) -> r
let (__proj__Node__item__left : interval_tree_aux -> interval_tree_aux) =
  fun projectee ->
    match projectee with | Node (mid, l, r, left, right) -> left
let (__proj__Node__item__right : interval_tree_aux -> interval_tree_aux) =
  fun projectee ->
    match projectee with | Node (mid, l, r, left, right) -> right
let rec (in_itv_tree : Interval.interval -> interval_tree_aux -> Prims.bool)
  =
  fun i ->
    fun it ->
      match it with
      | Empty -> false
      | Node (m, l, r, left, right) ->
          ((FStar_List_Tot_Base.mem i l) || (in_itv_tree i left)) ||
            (in_itv_tree i right)
let rec (count_itv_tree :
  Interval.interval -> interval_tree_aux -> Prims.nat) =
  fun i ->
    fun it ->
      match it with
      | Empty -> Prims.int_zero
      | Node (m, l, r, left, right) ->
          ((QuickSort_List.count i l) + (count_itv_tree i left)) +
            (count_itv_tree i right)
let rec (to_itvs : interval_tree_aux -> Interval.interval Prims.list) =
  fun it ->
    match it with
    | Empty -> []
    | Node (uu___, l, r, left, right) ->
        let ll = to_itvs left in
        let rr = to_itvs right in
        FStar_List_Tot_Base.op_At l (FStar_List_Tot_Base.op_At ll rr)
let rec check_list : 'a . 'a Prims.list -> ('a -> Prims.bool) -> Prims.bool =
  fun l ->
    fun f ->
      match l with | [] -> true | hd::tl -> (f hd) && (check_list tl f)
let (func_left : Interval.interval QuickSort_List.total_order) =
  let f i1 i2 =
    if i1.Interval.lbound < i2.Interval.lbound
    then true
    else
      if i1.Interval.lbound > i2.Interval.lbound
      then false
      else i1.Interval.rbound <= i2.Interval.rbound in
  f
let (func_right : Interval.interval QuickSort_List.total_order) =
  let f i1 i2 =
    if i1.Interval.rbound > i2.Interval.rbound
    then true
    else
      if i1.Interval.rbound < i2.Interval.rbound
      then false
      else i1.Interval.lbound >= i2.Interval.lbound in
  f
let rec remove : 'a . 'a -> 'a Prims.list -> 'a Prims.list =
  fun x ->
    fun l ->
      match l with
      | [] -> []
      | hd::tl -> if x = hd then tl else hd :: (remove x tl)
let rec (compute_bounds :
  Interval.interval Prims.list -> Prims.nat Prims.list) =
  fun itvs ->
    match itvs with
    | [] -> []
    | hd::tl -> (hd.Interval.lbound) :: (hd.Interval.rbound) ::
        (compute_bounds tl)
let (median_helper : Prims.nat Prims.list -> Prims.nat) =
  fun l ->
    let n = FStar_List_Tot_Base.length l in
    if (n mod (Prims.of_int (2))) = Prims.int_one
    then (n - Prims.int_one) / (Prims.of_int (2))
    else n / (Prims.of_int (2))
let rec my_ind : 'a . 'a Prims.list -> Prims.nat -> 'a =
  fun l ->
    fun i ->
      match l with
      | h::t ->
          if i = Prims.int_zero then h else my_ind t (i - Prims.int_one)
let (median_bounds : Interval.interval Prims.list -> Prims.nat) =
  fun itvs ->
    let bounds = compute_bounds itvs in
    let sorted_bounds =
      QuickSort_List.quicksort (fun x -> fun y -> x <= y) bounds in
    let mid_ind = median_helper sorted_bounds in
    let mid = my_ind sorted_bounds mid_ind in mid
let rec (ordered : interval_tree_aux -> Prims.bool) =
  fun it ->
    match it with
    | Empty -> true
    | Node (mid, l, r, left, right) ->
        (((((((((FStar_List_Tot_Base.length l) > Prims.int_zero) &&
                 (check_list (to_itvs left) (Interval.is_before mid)))
                && (check_list (to_itvs right) (Interval.is_after mid)))
               && (check_list l (Interval.contains mid)))
              && (QuickSort_List.sorted func_left l))
             && (QuickSort_List.sorted func_right r))
            && (mid = (median_bounds (to_itvs it))))
           && (ordered left))
          && (ordered right)
type interval_tree = interval_tree_aux
let (partition_upd :
  Interval.interval Prims.list ->
    (Interval.interval -> Prims.bool) ->
      (Interval.interval -> Prims.bool) ->
        (Interval.interval Prims.list * Interval.interval Prims.list *
          Interval.interval Prims.list))
  =
  fun itvs ->
    fun f1 ->
      fun f2 ->
        let uu___ = QuickSort_List.partition f1 itvs in
        match uu___ with
        | (left_itvs, maybe_right_itvs) ->
            let uu___1 = QuickSort_List.partition f2 maybe_right_itvs in
            (match uu___1 with
             | (right_itvs, mid_itvs) -> (left_itvs, mid_itvs, right_itvs))
let rec (count_bounds :
  Interval.interval Prims.list -> Prims.nat -> Prims.nat) =
  fun itvs ->
    fun b ->
      match itvs with
      | [] -> Prims.int_zero
      | hd::tl ->
          if hd.Interval.lbound = hd.Interval.rbound
          then
            (if hd.Interval.lbound = b
             then (Prims.of_int (2)) + (count_bounds tl b)
             else count_bounds tl b)
          else
            if (hd.Interval.lbound = b) || (hd.Interval.rbound = b)
            then Prims.int_one + (count_bounds tl b)
            else count_bounds tl b
let get_hd : 'a . 'a Prims.list -> 'a =
  fun l -> match l with | hd::uu___ -> hd
let get_tl : 'a . 'a Prims.list -> 'a Prims.list =
  fun l -> match l with | uu___::tl -> tl
let (get_left :
  Interval.interval Prims.list ->
    (Interval.interval -> Prims.bool) ->
      (Interval.interval -> Prims.bool) -> Interval.interval Prims.list)
  =
  fun intervals ->
    fun f1 ->
      fun f2 ->
        let p = partition_upd intervals f1 f2 in
        match p with | (left, uu___, uu___1) -> left
let (get_mid :
  Interval.interval Prims.list ->
    (Interval.interval -> Prims.bool) ->
      (Interval.interval -> Prims.bool) -> Interval.interval Prims.list)
  =
  fun intervals ->
    fun f1 ->
      fun f2 ->
        let p = partition_upd intervals f1 f2 in
        match p with | (uu___, mid, uu___1) -> mid
let (get_right :
  Interval.interval Prims.list ->
    (Interval.interval -> Prims.bool) ->
      (Interval.interval -> Prims.bool) -> Interval.interval Prims.list)
  =
  fun intervals ->
    fun f1 ->
      fun f2 ->
        let p = partition_upd intervals f1 f2 in
        match p with | (uu___, uu___1, right) -> right
let rec (create : Interval.interval Prims.list -> interval_tree) =
  fun intervals ->
    match intervals with
    | [] -> Empty
    | intervals1 ->
        let mid = median_bounds intervals1 in
        let uu___ =
          partition_upd intervals1 (Interval.is_before mid)
            (Interval.is_after mid) in
        (match uu___ with
         | (left_list, mid_list, right_list) ->
             let l = QuickSort_List.quicksort func_left mid_list in
             let r = QuickSort_List.quicksort func_right mid_list in
             let left = create left_list in
             let right = create right_list in
             let l_itvs = to_itvs left in
             let r_itvs = to_itvs right in
             let it = Node (mid, l, r, left, right) in
             let it_itvs = to_itvs it in it)
let rec (filter_left :
  Prims.nat ->
    Interval.interval Prims.list -> Prims.nat -> Interval.interval Prims.list)
  =
  fun xmid ->
    fun l ->
      fun qx ->
        match l with
        | [] -> []
        | hd::tl ->
            if Interval.contains qx hd
            then hd :: (filter_left xmid tl qx)
            else []
let rec (filter_right :
  Prims.nat ->
    Interval.interval Prims.list -> Prims.nat -> Interval.interval Prims.list)
  =
  fun xmid ->
    fun l ->
      fun qx ->
        match l with
        | [] -> []
        | hd::tl ->
            if Interval.contains qx hd
            then hd :: (filter_right xmid tl qx)
            else []
let rec (query : Prims.nat -> interval_tree -> Interval.interval Prims.list)
  =
  fun qx ->
    fun it ->
      match it with
      | Empty -> []
      | Node (mid, l, r, left, right) ->
          if qx < mid
          then
            FStar_List_Tot_Base.op_At (filter_left mid l qx) (query qx left)
          else
            FStar_List_Tot_Base.op_At (filter_right mid r qx)
              (query qx right)