open Prims
type interval_aux = {
  lbound: Prims.nat ;
  rbound: Prims.nat }
let (__proj__Mkinterval_aux__item__lbound : interval_aux -> Prims.nat) =
  fun projectee -> match projectee with | { lbound; rbound;_} -> lbound
let (__proj__Mkinterval_aux__item__rbound : interval_aux -> Prims.nat) =
  fun projectee -> match projectee with | { lbound; rbound;_} -> rbound
let (ordered : interval_aux -> Prims.bool) = fun i -> i.rbound >= i.lbound
type interval = interval_aux
let (create : Prims.nat -> Prims.nat -> interval) =
  fun lbound -> fun rbound -> { lbound; rbound }
let (is_before : Prims.nat -> interval -> Prims.bool) =
  fun x_mid -> fun itv -> itv.rbound < x_mid
let (is_after : Prims.nat -> interval -> Prims.bool) =
  fun x_mid -> fun itv -> itv.lbound > x_mid
let (contains : Prims.nat -> interval -> Prims.bool) =
  fun x_mid -> fun itv -> (itv.lbound <= x_mid) && (x_mid <= itv.rbound)
let (to_triplet : interval -> (Prims.nat * Prims.nat)) =
  fun itv -> ((itv.lbound), (itv.rbound))