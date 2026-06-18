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

// REPEAT 1 - TIME: 2.677906 s

method {:test} Test1() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 2 - TIME: 3.6822844 s

method {:test} Test2() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 3 - TIME: 4.7209641 s

method {:test} Test3() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 4 - TIME: 5.470057 s

method {:test} Test4() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 5 - TIME: 6.3264688 s

method {:test} Test5() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 6 - TIME: 7.307555 s

method {:test} Test6() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 7 - TIME: 8.2154832 s

method {:test} Test7() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 8 - TIME: 9.1161341 s

method {:test} Test8() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 9 - TIME: 9.8972181 s

method {:test} Test9() {
var mapint0 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var mapint1 : map<int, int> := map[0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0, 0 := 0];
var r0 := update_map<int,int>(mapint0, mapint1);
expect forall k :: k in mapint1 ==> k in r0;
expect forall k :: k in mapint0 ==> k in r0;
expect forall k :: k in mapint1 ==> r0[k] == mapint1[k];
expect forall k :: !(k in mapint1) && k in mapint0 ==> r0[k] == mapint0[k];
expect forall k :: !(k in mapint1) && !(k in mapint0) ==> !(k in r0);
}

// REPEAT 10 - TIME: 10.6102338 s
