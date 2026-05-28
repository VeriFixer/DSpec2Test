// vfag_tmp_tmpc29dxm1j_Verificacion_torneo.dfy

method {:testEntry} torneo(Valores: seq<real>, i: int, j: int, k: int)
    returns (pos_padre: int, pos_madre: int)
  requires |Valores| >= 20 && |Valores| < 50 && i >= 0 && j >= 0 && k >= 0
  requires i < |Valores| && j < |Valores| && k < |Valores| && i != j && j != k && k != i
  ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q
{
  assert (Valores[i] < Valores[j] && ((Valores[j] < Valores[k] && exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]))))) || (Valores[i] >= Valores[j] && ((Valores[j] >= Valores[k] && exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r])))));
  if Valores[i] == Valores[j] {
    assert (Valores[j] < Valores[k] && exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r])));
    if Valores[j] < Valores[k] {
      assert exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r];
      pos_padre := k;
      assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != j && j != r && p != r :: Valores[p] >= Valores[j] >= Valores[r] && pos_padre == p;
      pos_madre := j;
      assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
    } else {
      assert (Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]);
      if Valores[i] < Valores[k] {
        assert exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r];
        pos_padre := j;
        assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != k && k != r && p != r :: Valores[p] >= Valores[k] >= Valores[r] && pos_padre == p;
        pos_madre := k;
        assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
      } else {
        assert exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r];
        pos_padre := j;
        assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != i && i != r && p != r :: Valores[p] >= Valores[i] >= Valores[r] && pos_padre == p;
        pos_madre := i;
        assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
      }
    }
  } else {
    assert (Valores[j] >= Valores[k] && exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r])));
    if Valores[j] >= Valores[k] {
      assert exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r];
      pos_padre := i;
      assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != j && j != r && p != r :: Valores[p] >= Valores[j] >= Valores[r] && pos_padre == p;
      pos_madre := j;
      assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
    } else {
      assert (Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r]);
      if Valores[i] < Valores[k] {
        assert exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r];
        pos_padre := k;
        assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != i && i != r && p != r :: Valores[p] >= Valores[i] >= Valores[r] && pos_padre == p;
        pos_madre := i;
        assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
      } else {
        assert exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r];
        pos_padre := i;
        assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != k && k != r && p != r :: Valores[p] >= Valores[k] >= Valores[r] && pos_padre == p;
        pos_madre := k;
        assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
      }
      assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
    }
    assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
  }
  assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
}

method {:test} Test0() {
var seqreal0 : seq<real> := [0.0, 0.0, 2240.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -590.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 2 >= 0 && 3 >= 0 && 17 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 < |seqreal0| && 3 < |seqreal0| && 17 < |seqreal0| && 2 != 3 && 3 != 17 && 17 != 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 2, 3, 17);
expect exists p, q, r | p in {2, 3, 17} && q in {2, 3, 17} && r in {2, 3, 17} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test1() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -6906.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -2455.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 20 >= 0 && 27 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 20 < |seqreal0| && 27 < |seqreal0| && 30 < |seqreal0| && 20 != 27 && 27 != 30 && 30 != 20, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 20, 27, 30);
expect exists p, q, r | p in {20, 27, 30} && q in {20, 27, 30} && r in {20, 27, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test2() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 590.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -840.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 10 >= 0 && 11 >= 0 && 18 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 < |seqreal0| && 11 < |seqreal0| && 18 < |seqreal0| && 10 != 11 && 11 != 18 && 18 != 10, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 10, 11, 18);
expect exists p, q, r | p in {10, 11, 18} && q in {10, 11, 18} && r in {10, 11, 18} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test3() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2445.0, 0.0, 0.0, 0.0, 0.0, -5184.0, 2446.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 14 >= 0 && 29 >= 0 && 33 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 14 < |seqreal0| && 29 < |seqreal0| && 33 < |seqreal0| && 14 != 29 && 29 != 33 && 33 != 14, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 14, 29, 33);
expect exists p, q, r | p in {14, 29, 33} && q in {14, 29, 33} && r in {14, 29, 33} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test4() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 840.0, 0.0, -6906.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 7 >= 0 && 8 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 < |seqreal0| && 8 < |seqreal0| && 9 < |seqreal0| && 7 != 8 && 8 != 9 && 9 != 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 7, 8, 9);
expect exists p, q, r | p in {7, 8, 9} && q in {7, 8, 9} && r in {7, 8, 9} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test5() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 8879.0, 0.0, 8880.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 17 >= 0 && 18 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 17 < |seqreal0| && 18 < |seqreal0| && 19 < |seqreal0| && 17 != 18 && 18 != 19 && 19 != 17, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 17, 18, 19);
expect exists p, q, r | p in {17, 18, 19} && q in {17, 18, 19} && r in {17, 18, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test6() {
var seqreal0 : seq<real> := [0.0, 0.0, 2616.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -867.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 2 >= 0 && 3 >= 0 && 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 < |seqreal0| && 3 < |seqreal0| && 14 < |seqreal0| && 2 != 3 && 3 != 14 && 14 != 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 2, 3, 14);
expect exists p, q, r | p in {2, 3, 14} && q in {2, 3, 14} && r in {2, 3, 14} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test7() {
var seqreal0 : seq<real> := [582.0, -1658.0, 582.0, 582.0, -1629.0, 0.0, 583.0, 584.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 583.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 6 >= 0 && 7 >= 0 && 18 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 < |seqreal0| && 7 < |seqreal0| && 18 < |seqreal0| && 6 != 7 && 7 != 18 && 18 != 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 6, 7, 18);
expect exists p, q, r | p in {6, 7, 18} && q in {6, 7, 18} && r in {6, 7, 18} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test8() {
var seqreal0 : seq<real> := [0.0, 0.0, 840.0, -8039.0, 0.0, 0.0, 0.0, 0.0, -6790.0, -6789.0, 0.0, 0.0, 0.0, 841.0, 0.0, 0.0, 0.0, 0.0, 0.0, 841.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 9 >= 0 && 13 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 < |seqreal0| && 13 < |seqreal0| && 19 < |seqreal0| && 9 != 13 && 13 != 19 && 19 != 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 9, 13, 19);
expect exists p, q, r | p in {9, 13, 19} && q in {9, 13, 19} && r in {9, 13, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test9() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 682.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2331.0, 0.0, 2332.0, 2333.0, 0.0, 0.0, 0.0, 2334.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 25 >= 0 && 26 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 25 < |seqreal0| && 26 < |seqreal0| && 30 < |seqreal0| && 25 != 26 && 26 != 30 && 30 != 25, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 25, 26, 30);
expect exists p, q, r | p in {25, 26, 30} && q in {25, 26, 30} && r in {25, 26, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test10() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5904.0, 0.0, 142001.0 / 25.0, 0.0, 0.0, 0.0, -2240.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 4.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 31 >= 0 && 33 >= 0 && 37 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 31 < |seqreal0| && 33 < |seqreal0| && 37 < |seqreal0| && 31 != 33 && 33 != 37 && 37 != 31, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 31, 33, 37);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {31, 33, 37} && q in {31, 33, 37} && r in {31, 33, 37} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test11() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 6.0, 0.0, 4.0, 0.0, 0.0, 288606063939751.0 / 40000000000.0, 8.0, -(69193936060249.0 / 40000000000.0), 0.0, 2.0, 0.0, -(305993936060249.0 / 40000000000.0), 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 35 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 35 < |seqreal0| && 29 != 31 && 31 != 35 && 35 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 35);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 35} && q in {29, 31, 35} && r in {29, 31, 35} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test12() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2240.0, 0.0, 0.0, 0.0, 853177.0 / 400.0, 0.0, 0.0, 0.0, -1653.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 28 >= 0 && 32 >= 0 && 36 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 28 < |seqreal0| && 32 < |seqreal0| && 36 < |seqreal0| && 28 != 32 && 32 != 36 && 36 != 28, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 28, 32, 36);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {28, 32, 36} && q in {28, 32, 36} && r in {28, 32, 36} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test13() {
var seqreal0 : seq<real> := [2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 4135.0, 0.0, 4668.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5903.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5904.0, 0.0, 0.0, 0.0, -(695951.0 / 125.0), 0.0, 0.0, 0.0, -(695826.0 / 125.0), 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 31 >= 0 && 35 >= 0 && 39 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 31 < |seqreal0| && 35 < |seqreal0| && 39 < |seqreal0| && 31 != 35 && 35 != 39 && 39 != 31, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 31, 35, 39);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {31, 35, 39} && q in {31, 35, 39} && r in {31, 35, 39} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test14() {
var seqreal0 : seq<real> := [4.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1323.0, 0.0, 0.0, 0.0, 490007.0 / 400.0, 2.0, 0.0, 0.0, -2240.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 39 >= 0 && 43 >= 0 && 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 39 < |seqreal0| && 43 < |seqreal0| && 47 < |seqreal0| && 39 != 43 && 43 != 47 && 47 != 39, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 39, 43, 47);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {39, 43, 47} && q in {39, 43, 47} && r in {39, 43, 47} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test15() {
var seqreal0 : seq<real> := [2.0, 8455.0, 0.0, 6000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5133.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 8456.0, 0.0, 0.0, 0.0, -(124899.0 / 25.0), 0.0, 0.0, 0.0, 8457.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 35 >= 0 && 39 >= 0 && 43 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 35 < |seqreal0| && 39 < |seqreal0| && 43 < |seqreal0| && 35 != 39 && 39 != 43 && 43 != 35, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 35, 39, 43);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {35, 39, 43} && q in {35, 39, 43} && r in {35, 39, 43} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test16() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5904.0, 2.0, 0.0, 0.0, -(695951.0 / 125.0), 0.0, 0.0, 0.0, -8879.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 4.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 27 >= 0 && 31 >= 0 && 35 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 27 < |seqreal0| && 31 < |seqreal0| && 35 < |seqreal0| && 27 != 31 && 31 != 35 && 35 != 27, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 27, 31, 35);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {27, 31, 35} && q in {27, 31, 35} && r in {27, 31, 35} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test17() {
var seqreal0 : seq<real> := [2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -7887.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -5271.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -5271.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -13492.0, 0.0, -13492.0, 0.0, -5270.0, -5269.0, 0.0, -8879.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 42 >= 0 && 43 >= 0 && 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 42 < |seqreal0| && 43 < |seqreal0| && 45 < |seqreal0| && 42 != 43 && 43 != 45 && 45 != 42, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 42, 43, 45);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {42, 43, 45} && q in {42, 43, 45} && r in {42, 43, 45} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test18() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(696975815250589.0 / 200000000000.0), 0.0, 0.0, 0.0, -(1632775815250589.0 / 200000000000.0), 0.0, 0.0, 0.0, -(2232175815250589.0 / 200000000000.0), 0.0, 0.0, 2.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 26 >= 0 && 30 >= 0 && 34 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 26 < |seqreal0| && 30 < |seqreal0| && 34 < |seqreal0| && 26 != 30 && 30 != 34 && 34 != 26, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 26, 30, 34);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {26, 30, 34} && q in {26, 30, 34} && r in {26, 30, 34} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test19() {
var seqreal0 : seq<real> := [2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 840.0, 3361.0 / 4.0, 0.0, 0.0, 1681.0 / 2.0, 0.0, 0.0, 0.0, 1681.0 / 2.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 28 >= 0 && 31 >= 0 && 35 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 28 < |seqreal0| && 31 < |seqreal0| && 35 < |seqreal0| && 28 != 31 && 31 != 35 && 35 != 28, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 28, 31, 35);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {28, 31, 35} && q in {28, 31, 35} && r in {28, 31, 35} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test20() {
var seqreal0 : seq<real> := [2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 974.0, 0.0, 0.0, 975.0, 0.0, 0.0, 0.0, 976.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 37 >= 0 && 40 >= 0 && 44 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 37 < |seqreal0| && 40 < |seqreal0| && 44 < |seqreal0| && 37 != 40 && 40 != 44 && 44 != 37, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 37, 40, 44);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {37, 40, 44} && q in {37, 40, 44} && r in {37, 40, 44} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test21() {
var seqreal0 : seq<real> := [0.0, 10.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 3.0, 0.0, 0.0, 1888.0, 0.0, 7.0, 0.0, -(8859361.0 / 1250.0), -8456.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 47 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 47 < |seqreal0| && 48 < |seqreal0| && 43 != 47 && 47 != 48 && 48 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 47, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 47, 48} && q in {43, 47, 48} && r in {43, 47, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test22() {
var seqreal0 : seq<real> := [3.0, 7.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1315.0, 0.0, 0.0, 0.0, 8221.0, 0.0, 8221.0, 8221.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 45 >= 0 && 47 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 45 < |seqreal0| && 47 < |seqreal0| && 48 < |seqreal0| && 45 != 47 && 47 != 48 && 48 != 45, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 45, 47, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {45, 47, 48} && q in {45, 47, 48} && r in {45, 47, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test23() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 10.0, 1888.0, 7.0, -(8859361.0 / 1250.0), 0.0, 3.0, -8456.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 45 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 45 < |seqreal0| && 48 < |seqreal0| && 43 != 45 && 45 != 48 && 48 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 45, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 45, 48} && q in {43, 45, 48} && r in {43, 45, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test24() {
var seqreal0 : seq<real> := [3.0, 7.0, 10.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1887.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -6699.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1888.0, 428072.0 / 625.0, 428697.0 / 625.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 46 >= 0 && 47 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 46 < |seqreal0| && 47 < |seqreal0| && 48 < |seqreal0| && 46 != 47 && 47 != 48 && 48 != 46, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 46, 47, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {46, 47, 48} && q in {46, 47, 48} && r in {46, 47, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test25() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 3.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7.0, 10.0, 1.0 / 2.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 44 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 44 < |seqreal0| && 48 < |seqreal0| && 43 != 44 && 44 != 48 && 48 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 44, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 44, 48} && q in {43, 44, 48} && r in {43, 44, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test26() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 3.0, 0.0, 7.0, 1653.0, 607749.0 / 1250.0, 10.0, 0.0, 0.0, -5904.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 44 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 44 < |seqreal0| && 48 < |seqreal0| && 43 != 44 && 44 != 48 && 48 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 44, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 44, 48} && q in {43, 44, 48} && r in {43, 44, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test27() {
var seqreal0 : seq<real> := [-742.0, 0.0, 0.0, 5.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -7620.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -2953.0, 0.0, 0.0, -10144.0, -742.0, 0.0, 0.0, -742.0, 0.0, 0.0, 0.0, 0.0, -10144.0, 0.0, 0.0, 0.0, 0.0, 0.0, -742.0, 0.0, 0.0, 0.0, 0.0, -741.0, 0.0, 0.0, -740.0, 0.0, -1323.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 46 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 46 < |seqreal0| && 48 < |seqreal0| && 43 != 46 && 46 != 48 && 48 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 46, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 46, 48} && q in {43, 46, 48} && r in {43, 46, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test28() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 3.0, 770171983552607.0 / 100000000000.0, -(124328016447393.0 / 100000000000.0), 0.0, 0.0, 0.0, -(716328016447393.0 / 100000000000.0)];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 44 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 44 < |seqreal0| && 48 < |seqreal0| && 43 != 44 && 44 != 48 && 48 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 44, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 44, 48} && q in {43, 44, 48} && r in {43, 44, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test29() {
var seqreal0 : seq<real> := [3.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1888.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1888.0, 0.0, 1889.0, 7794.0, 0.0, 7794.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 45 >= 0 && 46 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 45 < |seqreal0| && 46 < |seqreal0| && 48 < |seqreal0| && 45 != 46 && 46 != 48 && 48 != 45, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 45, 46, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {45, 46, 48} && q in {45, 46, 48} && r in {45, 46, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test30() {
var seqreal0 : seq<real> := [3.0, 0.0, 0.0, 7.0, 1235.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1235.0, 1235.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1236.0, 1237.0, 0.0, 0.0, 1238.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 44 >= 0 && 45 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 44 < |seqreal0| && 45 < |seqreal0| && 48 < |seqreal0| && 44 != 45 && 45 != 48 && 48 != 44, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 44, 45, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {44, 45, 48} && q in {44, 45, 48} && r in {44, 45, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
