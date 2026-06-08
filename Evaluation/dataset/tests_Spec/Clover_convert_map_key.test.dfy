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

// REPEAT 1 - TIME: 2.5998356 s

method {:test} Test1() {
var mapnat0 : map<nat, bool> := map[(4287 as nat) := false, (4286 as nat) := false, (610 as nat) := false, (609 as nat) := true, (4285 as nat) := false, (3048 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 2 - TIME: 3.9125449 s

method {:test} Test2() {
var mapnat0 : map<nat, bool> := map[(4820 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (4818 as nat) := false, (3581 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 3 - TIME: 4.9817748 s

method {:test} Test3() {
var mapnat0 : map<nat, bool> := map[(4820 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (4818 as nat) := false, (3581 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 4 - TIME: 5.9010515 s

method {:test} Test4() {
var mapnat0 : map<nat, bool> := map[(4820 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (4818 as nat) := false, (3581 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 5 - TIME: 6.8794329 s

method {:test} Test5() {
var mapnat0 : map<nat, bool> := map[(4820 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (4818 as nat) := false, (3581 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 6 - TIME: 7.8835519 s

method {:test} Test6() {
var mapnat0 : map<nat, bool> := map[(4818 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (3581 as nat) := false, (4820 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 7 - TIME: 9.0756215 s

method {:test} Test7() {
var mapnat0 : map<nat, bool> := map[(4820 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (4818 as nat) := false, (3581 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 8 - TIME: 10.0234699 s

method {:test} Test8() {
var mapnat0 : map<nat, bool> := map[(4818 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (3581 as nat) := false, (4820 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 9 - TIME: 10.9070041 s

method {:test} Test9() {
var mapnat0 : map<nat, bool> := map[(4818 as nat) := false, (4819 as nat) := false, (1143 as nat) := false, (1142 as nat) := true, (3581 as nat) := false, (4820 as nat) := false];
var arrow0 : nat ~> nat := (a0:nat)=>0;
expect forall n1: nat, n2: nat :: n1 != n2 ==> arrow0(n1) != arrow0(n2), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := convert_map_key(mapnat0, arrow0);
expect forall k :: k in mapnat0 <==> arrow0(k) in r0;
expect forall k :: k in mapnat0 ==> r0[arrow0(k)] == mapnat0[k];
}

// REPEAT 10 - TIME: 11.9050987 s
