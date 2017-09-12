Require Import Arith ExtensionalMaps.

Module patch.
  Definition t := nat.
End patch.

Module patch_map.
  Definition class : Type := map.class patch.t.

  Definition instance : class := (sortedmap.sortedmap (lt := lt) _ _ _ _ _ _).

  Definition t V := @map.t _ instance V.
End patch_map.

Module parcel.
  Definition t := patch_map.t bool.
End parcel.

