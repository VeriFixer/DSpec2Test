// vfag_tmp_tmpc29dxm1j_Verificacion_torneo.dfy

method {:testEntry} torneo(Valores: seq<real>, i: int, j: int, k: int)
    returns (pos_padre: int, pos_madre: int)
  requires |Valores| >= 20 && |Valores| < 50 && i >= 0 && j >= 0 && k >= 0
  requires i < |Valores| && j < |Valores| && k < |Valores| && i != j && j != k && k != i
  ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q
{
  assert (Valores[i] < Valores[j] && ((Valores[j] < Valores[k] && exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]))))) || (Valores[i] >= Valores[j] && ((Valores[j] >= Valores[k] && exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r])))));
  if Valores[i] >= Valores[j] {
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
