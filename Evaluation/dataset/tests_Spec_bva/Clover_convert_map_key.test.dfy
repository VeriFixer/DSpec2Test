method {:testEntry} convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
{
  r:= map k | k in inputs :: f(k) := inputs[k];
}

method {:test} Test0() {
var mapnat0 : map<nat, bool> := map[(609 as nat) := false, (610 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}
method {:test} Test1() {
var mapnat0 : map<nat, bool> := map[];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}
method {:test} Test2() {
var mapnat0 : map<nat, bool> := map[(4818 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (3581 as nat) := false, (4820 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}
method {:test} Test6() {
var mapnat0 : map<nat, bool> := map[(5853 as nat) := false, (5854 as nat) := false, (8137 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 1 - TIME: 6.4551748 s

method {:test} Test10() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 2 - TIME: 7.3175732 s

method {:test} Test11() {
var mapnat0 : map<nat, bool> := map[(4818 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (3581 as nat) := false, (4820 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 3 - TIME: 8.0840224 s

method {:test} Test12() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 4 - TIME: 8.9480981 s

method {:test} Test13() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 5 - TIME: 9.5972579 s

method {:test} Test14() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 6 - TIME: 10.3653787 s

method {:test} Test15() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 7 - TIME: 10.9726851 s

method {:test} Test16() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 8 - TIME: 11.5879389 s

method {:test} Test17() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 9 - TIME: 12.246579 s

method {:test} Test18() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 10 - TIME: 12.8921215 s
