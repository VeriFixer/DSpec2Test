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
