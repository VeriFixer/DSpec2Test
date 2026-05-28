method {:testEntry} torneo(Valores : seq<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires |Valores| >= 20 && |Valores| < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < |Valores| && j < |Valores| && k < |Valores| && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q // Q

{
    
    assert (Valores[i] < Valores[j] && ((Valores[j] < Valores[k] && exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]))))) || (Valores[i] >= Valores[j] && ((Valores[j] >= Valores[k] && exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r]))))) ; // R : pmd(if..., Q)

        if Valores[i] < Valores[j] {

            assert (Valores[j] < Valores[k] && exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]))) ; // R1 : pmd(if..., Q)
        
                if Valores[j] < Valores[k] {

                    assert exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r] ; // R11 : pmd(pos_padre := k, R12)

                        pos_padre := k ;
            
                    assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != j && j != r && p != r :: Valores[p] >= Valores[j] >= Valores[r] && pos_padre == p ; // R12 : pmd(pos_madre := j, Q)   

                        pos_madre := j ;

                    assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                } else {

                    assert (Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]) ; // R2 : pmd(if..., Q)
            
                        if Valores[i] < Valores[k] {

                            assert exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r] ; // R13 : pmd(pos_padre := j, R14)

                                pos_padre := j ;

                            assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != k && k != r && p != r :: Valores[p] >= Valores[k] >= Valores[r] && pos_padre == p ; // R14 : pmd(pos_madre := k, Q)   

                                pos_madre := k ;

                            assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                        } else {

                            assert exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r] ; // R15 : pmd(pos_padre := j, R16)

                                pos_padre := j ;

                            assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != i && i != r && p != r :: Valores[p] >= Valores[i] >= Valores[r] && pos_padre == p ; // R16 : pmd(pos_madre := i, Q)   

                                pos_madre := i ;

                            assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                        }

                }

        } else {

            assert (Valores[j] >= Valores[k] && exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r]))) ; // R3 : pmd(if..., Q)

                if Valores[j] >= Valores[k] {
            
                    assert exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r] ; // R17 : pmd(pos_padre := i, R18)  

                        pos_padre := i ;

                    assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != j && j != r && p != r :: Valores[p] >= Valores[j] >= Valores[r] && pos_padre == p ; // R18 : pmd(pos_madre := j, Q)  

                        pos_madre := j ;

                    assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                } else {

                    assert (Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r]) ; // R4 : pmd(if..., Q)

                        if Valores[i] < Valores[k] {

                            assert exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r] ; // R19 : pmd(pos_padre := k, R110)  

                                pos_padre := k ;

                            assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != i && i != r && p != r :: Valores[p] >= Valores[i] >= Valores[r] && pos_padre == p ; // R110 : pmd(pos_madre := i, Q)  

                                pos_madre := i ;

                            assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                        } else {

                            assert exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r] ; // R111 : pmd(pos_padre := i, R112)  

                                pos_padre := i ;

                            assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != k && k != r && p != r :: Valores[p] >= Valores[k] >= Valores[r] && pos_padre == p ; // R112 : pmd(pos_madre := k, Q)  

                                pos_madre := k ;

                            assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q
           
                        }

                        assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q
               
                }

                assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q
        
        }

        assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

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
