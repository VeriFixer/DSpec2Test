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
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -38.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test3() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 38.0, -7719.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test5() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -38.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 18 >= 0 && 17 >= 0 && 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 18 < |seqreal0| && 17 < |seqreal0| && 19 < |seqreal0| && 18 != 17 && 17 != 19 && 19 != 18, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 18, 17, 19);
expect exists p, q, r | p in {18, 17, 19} && q in {18, 17, 19} && r in {18, 17, 19} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test6() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7719.0, -(3707329.0 / 2500.0), 2385171.0 / 2500.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 30 < |seqreal0| && 29 != 31 && 31 != 30 && 30 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 30);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 30} && q in {29, 31, 30} && r in {29, 31, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test7() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7719.0, 0.0, -1236.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 30 < |seqreal0| && 29 != 31 && 31 != 30 && 30 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 30);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 30} && q in {29, 31, 30} && r in {29, 31, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test8() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 18523809.0 / 10000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 3.0, -(70026191.0 / 10000.0), 7719.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 19 >= 0 && 45 >= 0 && 44 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 19 < |seqreal0| && 45 < |seqreal0| && 44 < |seqreal0| && 19 != 45 && 45 != 44 && 44 != 19, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 19, 45, 44);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {19, 45, 44} && q in {19, 45, 44} && r in {19, 45, 44} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test9() {
var seqreal0 : seq<real> := [7.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(28783333.0 / 2000.0), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(11073333.0 / 2000.0), 1236.0, 1.0, 3.0, 5.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 19 >= 0 && 34 >= 0 && 33 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 19 < |seqreal0| && 34 < |seqreal0| && 33 < |seqreal0| && 19 != 34 && 34 != 33 && 33 != 19, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 19, 34, 33);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {19, 34, 33} && q in {19, 34, 33} && r in {19, 34, 33} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test10() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2385171.0 / 2500.0, 7719.0, -(3707329.0 / 2500.0)];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 29 >= 0 && 31 >= 0 && 30 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 29 < |seqreal0| && 31 < |seqreal0| && 30 < |seqreal0| && 29 != 31 && 31 != 30 && 30 != 29, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 29, 31, 30);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {29, 31, 30} && q in {29, 31, 30} && r in {29, 31, 30} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test11() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(21390587.0 / 2500.0), 3.0, 5236913.0 / 2500.0, -(16900587.0 / 2500.0), 1.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 38 >= 0 && 41 >= 0 && 40 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 38 < |seqreal0| && 41 < |seqreal0| && 40 < |seqreal0| && 38 != 41 && 41 != 40 && 40 != 38, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 38, 41, 40);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {38, 41, 40} && q in {38, 41, 40} && r in {38, 41, 40} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test12() {
var seqreal0 : seq<real> := [8.0, 12.0, 10.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1892667.0 / 2000.0, 5484667.0 / 2000.0, -(14303333.0 / 2000.0)];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 47 >= 0 && 46 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 47 < |seqreal0| && 46 < |seqreal0| && 48 < |seqreal0| && 47 != 46 && 46 != 48 && 48 != 47, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 47, 46, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {47, 46, 48} && q in {47, 46, 48} && r in {47, 46, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test13() {
var seqreal0 : seq<real> := [2282.0, 13.0, 15.0, 11.0, 9.0, 17.0, 19.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(76246191.0 / 10000.0), 30263809.0 / 10000.0, -(58286191.0 / 10000.0)];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 47 >= 0 && 46 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 47 < |seqreal0| && 46 < |seqreal0| && 48 < |seqreal0| && 47 != 46 && 46 != 48 && 48 != 47, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 47, 46, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {47, 46, 48} && q in {47, 46, 48} && r in {47, 46, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test14() {
var seqreal0 : seq<real> := [14.0, 10.0, 8.0, 12.0, 16.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 4176069.0 / 500.0, 3278069.0 / 500.0, -(904431.0 / 500.0)];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 47 >= 0 && 46 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 47 < |seqreal0| && 46 < |seqreal0| && 48 < |seqreal0| && 47 != 46 && 46 != 48 && 48 != 47, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 47, 46, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {47, 46, 48} && q in {47, 46, 48} && r in {47, 46, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test15() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5484667.0 / 2000.0, 674667.0 / 2000.0, 1892667.0 / 2000.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 47 >= 0 && 46 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 47 < |seqreal0| && 46 < |seqreal0| && 48 < |seqreal0| && 47 != 46 && 46 != 48 && 48 != 47, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 47, 46, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {47, 46, 48} && q in {47, 46, 48} && r in {47, 46, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test16() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 8.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(14665333.0 / 2000.0), -(11073333.0 / 2000.0), 5656667.0 / 2000.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 47 >= 0 && 46 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 47 < |seqreal0| && 46 < |seqreal0| && 48 < |seqreal0| && 47 != 46 && 46 != 48 && 48 != 47, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 47, 46, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {47, 46, 48} && q in {47, 46, 48} && r in {47, 46, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test17() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(42472131817.0 / 6250000.0), -(21384467.0 / 2500.0), -(28209631817.0 / 6250000.0)];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 47 >= 0 && 46 >= 0 && 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 47 < |seqreal0| && 46 < |seqreal0| && 48 < |seqreal0| && 47 != 46 && 46 != 48 && 48 != 47, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 47, 46, 48);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {47, 46, 48} && q in {47, 46, 48} && r in {47, 46, 48} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test18() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1236.0, 0.0, -2437.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 44 >= 0 && 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 44 < |seqreal0| && 45 < |seqreal0| && 43 != 44 && 44 != 45 && 45 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 44, 45);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 44, 45} && q in {43, 44, 45} && r in {43, 44, 45} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test19() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1236.0, -2437.0, 1630883.0 / 2000.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 44 >= 0 && 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 44 < |seqreal0| && 45 < |seqreal0| && 43 != 44 && 44 != 45 && 45 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 44, 45);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 44, 45} && q in {43, 44, 45} && r in {43, 44, 45} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test20() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2437.0, -1236.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 44 >= 0 && 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 44 < |seqreal0| && 45 < |seqreal0| && 43 != 44 && 44 != 45 && 45 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 44, 45);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 44, 45} && q in {43, 44, 45} && r in {43, 44, 45} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test21() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1236.0, 2437.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 44 >= 0 && 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 44 < |seqreal0| && 45 < |seqreal0| && 43 != 44 && 44 != 45 && 45 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 44, 45);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 44, 45} && q in {43, 44, 45} && r in {43, 44, 45} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test22() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1236.0, 2437.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 44 >= 0 && 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 44 < |seqreal0| && 45 < |seqreal0| && 43 != 44 && 44 != 45 && 45 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 44, 45);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 44, 45} && q in {43, 44, 45} && r in {43, 44, 45} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test23() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1236.0, 0.0, 2437.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 43 >= 0 && 44 >= 0 && 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 43 < |seqreal0| && 44 < |seqreal0| && 45 < |seqreal0| && 43 != 44 && 44 != 45 && 45 != 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 43, 44, 45);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {43, 44, 45} && q in {43, 44, 45} && r in {43, 44, 45} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test24() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2437.0, 0.0, 0.0, 0.0, -1236.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 42 >= 0 && 43 >= 0 && 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 42 < |seqreal0| && 43 < |seqreal0| && 46 < |seqreal0| && 42 != 43 && 43 != 46 && 46 != 42, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 42, 43, 46);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {42, 43, 46} && q in {42, 43, 46} && r in {42, 43, 46} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test25() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2437.0, -1236.0, 0.0, 0.0, 0.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 42 >= 0 && 43 >= 0 && 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 42 < |seqreal0| && 43 < |seqreal0| && 46 < |seqreal0| && 42 != 43 && 43 != 46 && 46 != 42, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 42, 43, 46);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {42, 43, 46} && q in {42, 43, 46} && r in {42, 43, 46} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test26() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2437.0, 0.0, 0.0, -1236.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 42 >= 0 && 43 >= 0 && 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 42 < |seqreal0| && 43 < |seqreal0| && 46 < |seqreal0| && 42 != 43 && 43 != 46 && 46 != 42, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 42, 43, 46);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {42, 43, 46} && q in {42, 43, 46} && r in {42, 43, 46} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test27() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -2437.0, 1236.0, 0.0, 0.0, 1630883.0 / 2000.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 42 >= 0 && 43 >= 0 && 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 42 < |seqreal0| && 43 < |seqreal0| && 46 < |seqreal0| && 42 != 43 && 43 != 46 && 46 != 42, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 42, 43, 46);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {42, 43, 46} && q in {42, 43, 46} && r in {42, 43, 46} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test28() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1630883.0 / 2000.0, -2437.0, 0.0, 0.0, 1236.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 42 >= 0 && 43 >= 0 && 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 42 < |seqreal0| && 43 < |seqreal0| && 46 < |seqreal0| && 42 != 43 && 43 != 46 && 46 != 42, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 42, 43, 46);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {42, 43, 46} && q in {42, 43, 46} && r in {42, 43, 46} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test29() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -2437.0, 1630883.0 / 2000.0, 0.0, 0.0, 1236.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 42 >= 0 && 43 >= 0 && 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 42 < |seqreal0| && 43 < |seqreal0| && 46 < |seqreal0| && 42 != 43 && 43 != 46 && 46 != 42, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 42, 43, 46);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {42, 43, 46} && q in {42, 43, 46} && r in {42, 43, 46} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test30() {
var seqreal0 : seq<real> := [0.0, 0.0, 23.0, 21.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5236913.0 / 2500.0, -(16900587.0 / 2500.0), 29.0, 27.0, 25.0, 18.0, -(21390587.0 / 2500.0), 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 41 >= 0 && 42 >= 0 && 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 41 < |seqreal0| && 42 < |seqreal0| && 47 < |seqreal0| && 41 != 42 && 42 != 47 && 47 != 41, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 41, 42, 47);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {41, 42, 47} && q in {41, 42, 47} && r in {41, 42, 47} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test31() {
var seqreal0 : seq<real> := [0.0, 0.0, 23.0, 18.0, 25.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7719.0, 21.0, 0.0, -(70026191.0 / 10000.0), 29.0, 27.0, 0.0, 0.0, 18523809.0 / 10000.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 39 >= 0 && 42 >= 0 && 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 39 < |seqreal0| && 42 < |seqreal0| && 47 < |seqreal0| && 39 != 42 && 42 != 47 && 47 != 39, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 39, 42, 47);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {39, 42, 47} && q in {39, 42, 47} && r in {39, 42, 47} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test32() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(16900587.0 / 2500.0), -(10808087.0 / 2500.0), 20.0, 2282.0, 22.0, 6.0, -(21390587.0 / 2500.0), 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 41 >= 0 && 42 >= 0 && 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 41 < |seqreal0| && 42 < |seqreal0| && 47 < |seqreal0| && 41 != 42 && 42 != 47 && 47 != 41, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 41, 42, 47);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {41, 42, 47} && q in {41, 42, 47} && r in {41, 42, 47} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test33() {
var seqreal0 : seq<real> := [0.0, 18.0, 0.0, 0.0, 25.0, 23.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(70026191.0 / 10000.0), 7719.0, 21.0, 27.0, 29.0, 0.0, 18523809.0 / 10000.0, 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 41 >= 0 && 42 >= 0 && 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 41 < |seqreal0| && 42 < |seqreal0| && 47 < |seqreal0| && 41 != 42 && 42 != 47 && 47 != 41, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 41, 42, 47);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {41, 42, 47} && q in {41, 42, 47} && r in {41, 42, 47} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test34() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(16900587.0 / 2500.0), 27.0, 18.0, -(39038087.0 / 2500.0), 25.0, 4.0, 21.0, 23.0, -(10808087.0 / 2500.0), 0.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 39 >= 0 && 42 >= 0 && 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 39 < |seqreal0| && 42 < |seqreal0| && 47 < |seqreal0| && 39 != 42 && 42 != 47 && 47 != 39, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 39, 42, 47);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {39, 42, 47} && q in {39, 42, 47} && r in {39, 42, 47} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
method {:test} Test35() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(21390587.0 / 2500.0), 6.0, 0.0, -(16900587.0 / 2500.0), 23.0, 21.0, 0.0, 0.0, -(10808087.0 / 2500.0), 2282.0];
expect |seqreal0| >= 20 && |seqreal0| < 50 && 39 >= 0 && 42 >= 0 && 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 39 < |seqreal0| && 42 < |seqreal0| && 47 < |seqreal0| && 39 != 42 && 42 != 47 && 47 != 39, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := torneo(seqreal0, 39, 42, 47);
expect exists p: int, q: int, r: int {:trigger seqreal0[r], seqreal0[q], seqreal0[p]} | p in {39, 42, 47} && q in {39, 42, 47} && r in {39, 42, 47} && p != q && q != r && p != r :: seqreal0[p] >= seqreal0[q] >= seqreal0[r] && r0 == p && r1 == q;
}
