method {:testEntry} update_map<K(!new), V>(m1: map<K, V>, m2: map<K, V>) returns (r: map<K, V>)
  ensures (forall k :: k in m2 ==> k in r)
  ensures (forall k :: k in m1 ==> k in r)
  ensures  (forall k :: k in m2 ==> r[k] == m2[k])
  ensures  (forall k :: !(k in m2) && k in m1 ==> r[k] == m1[k])
  ensures  (forall k :: !(k in m2) && !(k in m1) ==> !(k in r))
{
  r:= map k | k in (m1.Keys + m2.Keys) :: if k in m2 then m2[k] else m1[k];
}

method {:test} Test0() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}
method {:test} Test1() {
var mapint0 : map<int, int> := map[];
var mapint1 : map<int, int> := map[];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}
method {:test} Test2() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}
method {:test} Test5() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}
method {:test} Test6() {
var mapint0 : map<int, int> := map[];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}
method {:test} Test9() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}
method {:test} Test11() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 1 - TIME: 12.2432122 s

method {:test} Test13() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 2 - TIME: 13.572431 s

method {:test} Test14() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 3 - TIME: 14.723228 s

method {:test} Test15() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 4 - TIME: 16.1229595 s

method {:test} Test16() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 5 - TIME: 17.4639919 s

method {:test} Test17() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 6 - TIME: 18.4853956 s

method {:test} Test18() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 7 - TIME: 19.2777699 s

method {:test} Test19() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 8 - TIME: 20.4156339 s

method {:test} Test20() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 9 - TIME: 21.3954832 s

method {:test} Test21() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 10 - TIME: 22.4944147 s
