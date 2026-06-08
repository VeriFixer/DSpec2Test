
method {:test} Test17() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 9 - TIME: 14.8717236 s