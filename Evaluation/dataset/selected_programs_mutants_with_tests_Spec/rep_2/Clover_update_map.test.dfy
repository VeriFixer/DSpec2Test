
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

// REPEAT 2 - TIME: 3.8918487 s