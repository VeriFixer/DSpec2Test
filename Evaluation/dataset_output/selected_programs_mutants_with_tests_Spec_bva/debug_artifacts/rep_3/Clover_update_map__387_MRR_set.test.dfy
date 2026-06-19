// Clover_update_map.dfy

method {:testEntry} update_map<K(!new), V>(m1: map<K, V>, m2: map<K, V>) returns (r: map<K, V>)
  ensures forall k :: k in m2 ==> k in r
  ensures forall k :: k in m1 ==> k in r
  ensures forall k :: k in m2 ==> r[k] == m2[k]
  ensures forall k :: !(k in m2) && k in m1 ==> r[k] == m1[k]
  ensures forall k :: !(k in m2) && !(k in m1) ==> !(k in r)
{
  r := map k | k in {} + m2.Keys :: if k in m2 then m2[k] else m1[k];
}

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

// REPEAT 3 - TIME: 10.5047552 s
