// Clover_update_map.dfy

method {:testEntry} update_map<K(!new), V>(m1: map<K, V>, m2: map<K, V>) returns (r: map<K, V>)
  ensures forall k :: k in m2 ==> k in r
  ensures forall k :: k in m1 ==> k in r
  ensures forall k :: k in m2 ==> r[k] == m2[k]
  ensures forall k :: !(k in m2) && k in m1 ==> r[k] == m1[k]
  ensures forall k :: !(k in m2) && !(k in m1) ==> !(k in r)
{
  r := map k | k in m1.Keys + m2.Keys :: m1[k];
}


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

// REPEAT 1 - TIME: 8.3639927 s

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

// REPEAT 2 - TIME: 9.2698138 s

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

// REPEAT 3 - TIME: 10.1072198 s

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

// REPEAT 4 - TIME: 10.8010609 s

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

// REPEAT 5 - TIME: 11.5869242 s

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

// REPEAT 6 - TIME: 12.2625202 s

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

// REPEAT 7 - TIME: 13.1778272 s

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

// REPEAT 8 - TIME: 14.0316932 s

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

// REPEAT 9 - TIME: 14.8260025 s

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

// REPEAT 10 - TIME: 15.5800032 s
