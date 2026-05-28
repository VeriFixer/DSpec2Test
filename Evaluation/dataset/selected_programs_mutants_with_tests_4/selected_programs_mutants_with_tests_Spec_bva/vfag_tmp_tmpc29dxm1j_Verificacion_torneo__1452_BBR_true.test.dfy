// vfag_tmp_tmpc29dxm1j_Verificacion_torneo.dfy

method {:testEntry} torneo(Valores: seq<real>, i: int, j: int, k: int)
    returns (pos_padre: int, pos_madre: int)
  requires |Valores| >= 20 && |Valores| < 50 && i >= 0 && j >= 0 && k >= 0
  requires i < |Valores| && j < |Valores| && k < |Valores| && i != j && j != k && k != i
  ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q
{
  assert (Valores[i] < Valores[j] && ((Valores[j] < Valores[k] && exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]))))) || (Valores[i] >= Valores[j] && ((Valores[j] >= Valores[k] && exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r])))));
  if true {
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
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -38.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test1() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, -2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 2 >= 0 && 1 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 < |seqreal0| && 1 < |seqreal0| && 3 < |seqreal0| && 2 != 1 && 1 != 3 && 3 != 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 2, 1, 3);
expect exists p, q, r | p in {2, 1, 3} && q in {2, 1, 3} && r in {2, 1, 3} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test2() {
var seqreal0 : seq<real> := [7719.0, 0.0, 0.0, 0.0, -1236.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 0 >= 0 && 3 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 < |seqreal0| && 3 < |seqreal0| && 4 < |seqreal0| && 0 != 3 && 3 != 4 && 4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 0, 3, 4);
expect exists p, q, r | p in {0, 3, 4} && q in {0, 3, 4} && r in {0, 3, 4} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test3() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, -7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 3 >= 0 && 0 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 < |seqreal0| && 0 < |seqreal0| && 4 < |seqreal0| && 3 != 0 && 0 != 4 && 4 != 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 3, 0, 4);
expect exists p, q, r | p in {3, 0, 4} && q in {3, 0, 4} && r in {3, 0, 4} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test4() {
var seqreal0 : seq<real> := [-1236.0, 0.0, 0.0, 0.0, 7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 4 >= 0 && 3 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 < |seqreal0| && 3 < |seqreal0| && 0 < |seqreal0| && 4 != 3 && 3 != 0 && 0 != 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 4, 3, 0);
expect exists p, q, r | p in {4, 3, 0} && q in {4, 3, 0} && r in {4, 3, 0} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test7() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 38.0, -7719.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test9() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -38.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test10() {
var seqreal0 : seq<real> := [0.0, -8855.0, 2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 2 >= 0 && 1 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 < |seqreal0| && 1 < |seqreal0| && 3 < |seqreal0| && 2 != 1 && 1 != 3 && 3 != 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 2, 1, 3);
expect exists p, q, r | p in {2, 1, 3} && q in {2, 1, 3} && r in {2, 1, 3} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test11() {
var seqreal0 : seq<real> := [7719.0, 0.0, 0.0, -1236.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 0 >= 0 && 3 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 < |seqreal0| && 3 < |seqreal0| && 4 < |seqreal0| && 0 != 3 && 3 != 4 && 4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 0, 3, 4);
expect exists p, q, r | p in {0, 3, 4} && q in {0, 3, 4} && r in {0, 3, 4} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test12() {
var seqreal0 : seq<real> := [-1236.0, 0.0, 0.0, 7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 3 >= 0 && 0 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 < |seqreal0| && 0 < |seqreal0| && 4 < |seqreal0| && 3 != 0 && 0 != 4 && 4 != 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 3, 0, 4);
expect exists p, q, r | p in {3, 0, 4} && q in {3, 0, 4} && r in {3, 0, 4} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test13() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, -1236.0, 7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 4 >= 0 && 3 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 < |seqreal0| && 3 < |seqreal0| && 0 < |seqreal0| && 4 != 3 && 3 != 0 && 0 != 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 4, 3, 0);
expect exists p, q, r | p in {4, 3, 0} && q in {4, 3, 0} && r in {4, 3, 0} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test14() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -7719.0, 38.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test20() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, -7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 0 >= 0 && 3 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 < |seqreal0| && 3 < |seqreal0| && 4 < |seqreal0| && 0 != 3 && 3 != 4 && 4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 0, 3, 4);
expect exists p, q, r | p in {0, 3, 4} && q in {0, 3, 4} && r in {0, 3, 4} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test22() {
var seqreal0 : seq<real> := [-7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 4 >= 0 && 3 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 < |seqreal0| && 3 < |seqreal0| && 0 < |seqreal0| && 4 != 3 && 3 != 0 && 0 != 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 4, 3, 0);
expect exists p, q, r | p in {4, 3, 0} && q in {4, 3, 0} && r in {4, 3, 0} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test27() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 38.0, -7719.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test28() {
var seqreal0 : seq<real> := [0.0, 0.0, -2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 2 >= 0 && 1 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 < |seqreal0| && 1 < |seqreal0| && 3 < |seqreal0| && 2 != 1 && 1 != 3 && 3 != 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 2, 1, 3);
expect exists p, q, r | p in {2, 1, 3} && q in {2, 1, 3} && r in {2, 1, 3} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test29() {
var seqreal0 : seq<real> := [-7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 0 >= 0 && 3 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 < |seqreal0| && 3 < |seqreal0| && 4 < |seqreal0| && 0 != 3 && 3 != 4 && 4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 0, 3, 4);
expect exists p, q, r | p in {0, 3, 4} && q in {0, 3, 4} && r in {0, 3, 4} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test30() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, -7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 3 >= 0 && 0 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 < |seqreal0| && 0 < |seqreal0| && 4 < |seqreal0| && 3 != 0 && 0 != 4 && 4 != 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 3, 0, 4);
expect exists p, q, r | p in {3, 0, 4} && q in {3, 0, 4} && r in {3, 0, 4} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test31() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, -7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 4 >= 0 && 3 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 < |seqreal0| && 3 < |seqreal0| && 0 < |seqreal0| && 4 != 3 && 3 != 0 && 0 != 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 4, 3, 0);
expect exists p, q, r | p in {4, 3, 0} && q in {4, 3, 0} && r in {4, 3, 0} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test32() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -38.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test37() {
var seqreal0 : seq<real> := [0.0, -8855.0, 0.0, 2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 2 >= 0 && 1 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 < |seqreal0| && 1 < |seqreal0| && 3 < |seqreal0| && 2 != 1 && 1 != 3 && 3 != 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 2, 1, 3);
expect exists p, q, r | p in {2, 1, 3} && q in {2, 1, 3} && r in {2, 1, 3} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test38() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, -7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 0 >= 0 && 3 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 < |seqreal0| && 3 < |seqreal0| && 4 < |seqreal0| && 0 != 3 && 3 != 4 && 4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 0, 3, 4);
expect exists p, q, r | p in {0, 3, 4} && q in {0, 3, 4} && r in {0, 3, 4} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test39() {
var seqreal0 : seq<real> := [-7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 3 >= 0 && 0 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 < |seqreal0| && 0 < |seqreal0| && 4 < |seqreal0| && 3 != 0 && 0 != 4 && 4 != 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 3, 0, 4);
expect exists p, q, r | p in {3, 0, 4} && q in {3, 0, 4} && r in {3, 0, 4} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test40() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, -7719.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 4 >= 0 && 3 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 < |seqreal0| && 3 < |seqreal0| && 0 < |seqreal0| && 4 != 3 && 3 != 0 && 0 != 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 4, 3, 0);
expect exists p, q, r | p in {4, 3, 0} && q in {4, 3, 0} && r in {4, 3, 0} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test41() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -7719.0, 0.0, 38.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test54() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7719.0, -1236.0, 1892667.0 / 2000.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 30 < |seqreal0| && 29 != 31 && 31 != 30 && 30 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 30);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 30} && q in {29, 31, 30} && r in {29, 31, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test55() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7719.0, 2385171.0 / 2500.0, -(3707329.0 / 2500.0)];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 30 < |seqreal0| && 29 != 31 && 31 != 30 && 30 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 30);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 30} && q in {29, 31, 30} && r in {29, 31, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test56() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1236.0, 7719.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 30 < |seqreal0| && 29 != 31 && 31 != 30 && 30 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 30);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 30} && q in {29, 31, 30} && r in {29, 31, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test57() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1236.0, 1892667.0 / 2000.0, 7719.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 30 < |seqreal0| && 29 != 31 && 31 != 30 && 30 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 30);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 30} && q in {29, 31, 30} && r in {29, 31, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test58() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2385171.0 / 2500.0, 7719.0, -(3707329.0 / 2500.0)];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 30 < |seqreal0| && 29 != 31 && 31 != 30 && 30 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 30);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 30} && q in {29, 31, 30} && r in {29, 31, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test59() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1236.0, 7719.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 30 < |seqreal0| && 29 != 31 && 31 != 30 && 30 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 30);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 30} && q in {29, 31, 30} && r in {29, 31, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test60() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7719.0, 0.0, -38.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 31 >= 0 && 32 >= 0 && 33 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 31 < |seqreal0| && 32 < |seqreal0| && 33 < |seqreal0| && 31 != 32 && 32 != 33 && 33 != 31, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 31, 32, 33);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {31, 32, 33} && q in {31, 32, 33} && r in {31, 32, 33} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test61() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(10808087.0 / 2500.0), -(39038087.0 / 2500.0), -(16900587.0 / 2500.0), 4.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 31 >= 0 && 32 >= 0 && 33 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 31 < |seqreal0| && 32 < |seqreal0| && 33 < |seqreal0| && 31 != 32 && 32 != 33 && 33 != 31, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 31, 32, 33);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {31, 32, 33} && q in {31, 32, 33} && r in {31, 32, 33} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test62() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 38.0, -7719.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 31 >= 0 && 32 >= 0 && 33 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 31 < |seqreal0| && 32 < |seqreal0| && 33 < |seqreal0| && 31 != 32 && 32 != 33 && 33 != 31, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 31, 32, 33);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {31, 32, 33} && q in {31, 32, 33} && r in {31, 32, 33} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test63() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(6033339.0 / 5000.0), 38.0, 146661.0 / 5000.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 31 >= 0 && 32 >= 0 && 33 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 31 < |seqreal0| && 32 < |seqreal0| && 33 < |seqreal0| && 31 != 32 && 32 != 33 && 33 != 31, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 31, 32, 33);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {31, 32, 33} && q in {31, 32, 33} && r in {31, 32, 33} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test64() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -38.0, 7719.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 31 >= 0 && 32 >= 0 && 33 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 31 < |seqreal0| && 32 < |seqreal0| && 33 < |seqreal0| && 31 != 32 && 32 != 33 && 33 != 31, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 31, 32, 33);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {31, 32, 33} && q in {31, 32, 33} && r in {31, 32, 33} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test65() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -38.0, 0.0, 7719.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 31 >= 0 && 32 >= 0 && 33 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 31 < |seqreal0| && 32 < |seqreal0| && 33 < |seqreal0| && 31 != 32 && 32 != 33 && 33 != 31, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 31, 32, 33);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {31, 32, 33} && q in {31, 32, 33} && r in {31, 32, 33} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test66() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7719.0, 1892667.0 / 2000.0, -1236.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 32 >= 0 && 33 >= 0 && 34 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 32 < |seqreal0| && 33 < |seqreal0| && 34 < |seqreal0| && 32 != 33 && 33 != 34 && 34 != 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 32, 33, 34);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {32, 33, 34} && q in {32, 33, 34} && r in {32, 33, 34} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test67() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1236.0, -7719.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 32 >= 0 && 33 >= 0 && 34 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 32 < |seqreal0| && 33 < |seqreal0| && 34 < |seqreal0| && 32 != 33 && 33 != 34 && 34 != 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 32, 33, 34);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {32, 33, 34} && q in {32, 33, 34} && r in {32, 33, 34} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test68() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1236.0, -7719.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 32 >= 0 && 33 >= 0 && 34 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 32 < |seqreal0| && 33 < |seqreal0| && 34 < |seqreal0| && 32 != 33 && 33 != 34 && 34 != 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 32, 33, 34);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {32, 33, 34} && q in {32, 33, 34} && r in {32, 33, 34} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test69() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -7719.0, 1236.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 32 >= 0 && 33 >= 0 && 34 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 32 < |seqreal0| && 33 < |seqreal0| && 34 < |seqreal0| && 32 != 33 && 33 != 34 && 34 != 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 32, 33, 34);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {32, 33, 34} && q in {32, 33, 34} && r in {32, 33, 34} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test70() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -7719.0, 1236.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 32 >= 0 && 33 >= 0 && 34 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 32 < |seqreal0| && 33 < |seqreal0| && 34 < |seqreal0| && 32 != 33 && 33 != 34 && 34 != 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 32, 33, 34);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {32, 33, 34} && q in {32, 33, 34} && r in {32, 33, 34} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test71() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -7719.0, 0.0, 1236.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 32 >= 0 && 33 >= 0 && 34 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 32 < |seqreal0| && 33 < |seqreal0| && 34 < |seqreal0| && 32 != 33 && 33 != 34 && 34 != 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 32, 33, 34);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {32, 33, 34} && q in {32, 33, 34} && r in {32, 33, 34} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
