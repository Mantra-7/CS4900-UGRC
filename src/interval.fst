module Interval

type interval_aux = {
  lbound: nat;
  rbound: nat
}

let ordered (i:interval_aux): Tot bool =
    i.rbound >= i.lbound

type interval = (i:interval_aux{ordered i})

val create (lbound:nat) (rbound:nat{rbound>=lbound}): interval
let create lbound rbound =
    { lbound ; rbound }

let is_before (x_mid:nat) (itv:interval) : Tot (b:bool{b <==> itv.rbound < x_mid}) =
    itv.rbound < x_mid

let is_after (x_mid:nat) (itv:interval) : Tot (b:bool{b <==> itv.lbound > x_mid}) =
    itv.lbound > x_mid

let contains (x_mid:nat) (itv:interval) : Tot (b:bool{b <==> (itv.rbound >= x_mid /\ itv.lbound <= x_mid)}) =
  (itv.lbound <= x_mid) && (x_mid <= itv.rbound)

let to_triplet (itv:interval) : Tot (nat * nat) =
    itv.lbound, itv.rbound
