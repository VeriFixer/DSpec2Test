datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
  decreases t 
{
  match t {
    case Leaf(v) => [ CLf(v) ]
    case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
    case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
  }
}

// Ex 1
function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
  requires |codes| > 0 || |trees| > 0
  ensures |deserialiseAux(codes, trees)| >= 0
  decreases codes
{
  if |codes| == 0 then trees
  else
    match codes[0] {
      case CLf(v) => deserialiseAux(codes[1..], trees + [Leaf(v)])
      case CSNd(v) => if (|trees| >= 1) then deserialiseAux(codes[1..], trees[..|trees|-1] + [SingleNode(v, trees[|trees|-1])]) else trees
      case CDNd(v) => if (|trees| >= 2) then deserialiseAux(codes[1..], trees[..|trees|-2] + [DoubleNode(v, trees[|trees|-1], trees[|trees|-2])]) else trees
    }
}

function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
  requires |s| > 0
{
  deserialiseAux(s, [])
}

// Ex 2
method {:testEntry} testSerializeWithASingleLeaf()
{
  var tree := Leaf(42);
  var result := serialise(tree);
  assert result == [CLf(42)];
}

method {:testEntry} testSerializeNullValues()
{
    var tree := Leaf(null);
    var result := serialise(tree);
    assert result == [CLf(null)];
}

method {:testEntry} testSerializeWithAllElements()
{
  var tree: Tree<int> := DoubleNode(9, Leaf(6), DoubleNode(2, Leaf(5), SingleNode(4, Leaf(3))));
  var codes := serialise(tree);
  assert |codes| == 6;
  var expectedCodes := [CLf(3), CSNd(4), CLf(5), CDNd(2), CLf(6), CDNd(9)];
  assert codes == expectedCodes;
}

// Ex 3 

method {:testEntry} testDeseraliseWithASingleLeaf() {
  var codes: seq<Code<int>> := [CLf(9)];
  var trees := deserialise(codes);
  assert |trees| == 1;
  var expectedTree := Leaf(9);
  assert trees[0] == expectedTree;
}

method {:testEntry} testDeserializeWithASingleNode()
{
  var codes: seq<Code<int>> := [CLf(3), CSNd(9), CLf(5)];
  var trees := deserialise(codes);
  assert |trees| == 2;
  var expectedTree1 := SingleNode(9, Leaf(3));
  var expectedTree2 := Leaf(5);
  assert trees[0] == expectedTree1;
  assert trees[1] == expectedTree2;
}

method {:testEntry} testDeserialiseWithAllElements()
{
    var codes: seq<Code<int>> := [CLf(3), CSNd(4), CLf(5), CDNd(2), CLf(6), CDNd(9)];
    var trees := deserialise(codes);
    assert |trees| == 1; 
    var expectedTree := DoubleNode(9, Leaf(6), DoubleNode(2, Leaf(5), SingleNode(4, Leaf(3))));
    assert trees[0] == expectedTree;
}

// Ex 4 
lemma SerialiseLemma<V>(t: Tree<V>)
  ensures deserialise(serialise(t)) == [t]
{
  assert serialise(t) + [] == serialise(t);

  calc{
    deserialise(serialise(t));
    ==
    deserialise(serialise(t) + []);
    ==
    deserialiseAux(serialise(t) + [], []);
    == { DeserialisetAfterSerialiseLemma(t, [], []); }
    deserialiseAux([],[] + [t]);
    ==
    deserialiseAux([],[t]);
    == 
    [t];
  }
}


lemma DeserialisetAfterSerialiseLemma<T> (t : Tree<T>, cds : seq<Code<T>>, ts : seq<Tree<T>>) 
  ensures deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, ts + [t])
  {
    match t{
      case Leaf(x) =>
        calc{
          deserialiseAux(serialise(t) + cds, ts);
          ==
            deserialiseAux([CLf(x)] + cds, ts);
          == 
            deserialiseAux(cds, ts + [Leaf(x)]);
          == 
            deserialiseAux(cds, ts + [t]);
        }
      case SingleNode(x,t1) =>
        assert serialise(t1) + [ CSNd(x) ] + cds ==  serialise(t1) + ([ CSNd(x) ] + cds);
        calc{
          deserialiseAux(serialise(t) + cds, ts);
          ==
            deserialiseAux( serialise(t1) + [CSNd(x)] + cds ,ts); 
          ==
            deserialiseAux((serialise(t1) + [CSNd(x)] + cds),ts);
          == { DeserialisetAfterSerialiseLemma(t1 , [ CSNd(x) ], ts); }
            deserialiseAux(serialise(t1)+ [CSNd(x)]  + cds, ts );
          ==
            deserialiseAux( ([CSNd(x)] + cds), ts + [ t1 ]);
          == 
            deserialiseAux(cds, ts + [SingleNode(x,t1)]);
          == 
            deserialiseAux(cds, ts + [t]); 
        }
      case DoubleNode(x,t1,t2) =>
        assert serialise(t2) + serialise(t1) + [ CDNd(x) ] + cds == serialise(t2) + (serialise(t1) + [ CDNd(x) ] + cds);
        assert serialise(t1) + [CDNd(x)] + cds == serialise(t1) + ([CDNd(x)] + cds); 
        assert  (ts + [ t2 ]) +  [ t1 ] == ts + [t2,t1];
        calc{
          deserialiseAux(serialise(t) + cds, ts);
          ==
            deserialiseAux(serialise(t2) + serialise(t1) + [CDNd(x)] + cds ,ts); 
          ==
            deserialiseAux(serialise(t2) + (serialise(t1) + [CDNd(x)] + cds),ts);
          == { DeserialisetAfterSerialiseLemma(t2, serialise(t1) + [ CDNd(x) ], ts); }
            deserialiseAux(serialise(t1)+ [CDNd(x)]  + cds, ts + [ t2 ]);
          ==
            deserialiseAux(serialise(t1) + ([CDNd(x)] + cds), ts + [ t2 ]);
          == { DeserialisetAfterSerialiseLemma(t1, [ CDNd(x) ] + cds, ts + [ t2 ]); }
            deserialiseAux([ CDNd(x) ] + cds, (ts + [ t2 ]) + [t1]);
          ==
            deserialiseAux([ CDNd(x) ] + cds, ts + [t2, t1]);
          == 
            deserialiseAux([CDNd(x)] + cds, ts + [t2 , t1]);
          == 
            deserialiseAux(cds, ts + [DoubleNode(x,t1,t2)]); 
          == 
            deserialiseAux(cds, ts + [t]);
        }
    }
  }

method {:test} Test0() {
testSerializeWithASingleLeaf();
}
method {:test} Test3() {
testSerializeNullValues();
}
method {:test} Test6() {
testSerializeWithAllElements();
}
method {:test} Test9() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test12() {
testDeserializeWithASingleNode();
}
method {:test} Test15() {
testDeserialiseWithAllElements();
}

// REPEAT 1 - TIME: 12.287386 s

method {:test} Test18() {
testSerializeWithASingleLeaf();
}
method {:test} Test19() {
testSerializeNullValues();
}
method {:test} Test20() {
testSerializeWithAllElements();
}
method {:test} Test21() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test22() {
testDeserializeWithASingleNode();
}
method {:test} Test23() {
testDeserialiseWithAllElements();
}

// REPEAT 2 - TIME: 15.5814437 s

method {:test} Test24() {
testSerializeWithASingleLeaf();
}
method {:test} Test25() {
testSerializeNullValues();
}
method {:test} Test26() {
testSerializeWithAllElements();
}
method {:test} Test27() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test28() {
testDeserializeWithASingleNode();
}
method {:test} Test29() {
testDeserialiseWithAllElements();
}

// REPEAT 3 - TIME: 18.396098 s

method {:test} Test30() {
testSerializeWithASingleLeaf();
}
method {:test} Test31() {
testSerializeNullValues();
}
method {:test} Test32() {
testSerializeWithAllElements();
}
method {:test} Test33() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test34() {
testDeserializeWithASingleNode();
}
method {:test} Test35() {
testDeserialiseWithAllElements();
}

// REPEAT 4 - TIME: 20.9589095 s

method {:test} Test36() {
testSerializeWithASingleLeaf();
}
method {:test} Test37() {
testSerializeNullValues();
}
method {:test} Test38() {
testSerializeWithAllElements();
}
method {:test} Test39() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test40() {
testDeserializeWithASingleNode();
}
method {:test} Test41() {
testDeserialiseWithAllElements();
}

// REPEAT 5 - TIME: 23.6812558 s

method {:test} Test42() {
testSerializeWithASingleLeaf();
}
method {:test} Test43() {
testSerializeNullValues();
}
method {:test} Test44() {
testSerializeWithAllElements();
}
method {:test} Test45() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test46() {
testDeserializeWithASingleNode();
}
method {:test} Test47() {
testDeserialiseWithAllElements();
}

// REPEAT 6 - TIME: 26.2870558 s

method {:test} Test48() {
testSerializeWithASingleLeaf();
}
method {:test} Test49() {
testSerializeNullValues();
}
method {:test} Test50() {
testSerializeWithAllElements();
}
method {:test} Test51() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test52() {
testDeserializeWithASingleNode();
}
method {:test} Test53() {
testDeserialiseWithAllElements();
}

// REPEAT 7 - TIME: 29.0334737 s

method {:test} Test54() {
testSerializeWithASingleLeaf();
}
method {:test} Test55() {
testSerializeNullValues();
}
method {:test} Test56() {
testSerializeWithAllElements();
}
method {:test} Test57() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test58() {
testDeserializeWithASingleNode();
}
method {:test} Test59() {
testDeserialiseWithAllElements();
}

// REPEAT 8 - TIME: 31.8131581 s

method {:test} Test60() {
testSerializeWithASingleLeaf();
}
method {:test} Test61() {
testSerializeNullValues();
}
method {:test} Test62() {
testSerializeWithAllElements();
}
method {:test} Test63() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test64() {
testDeserializeWithASingleNode();
}
method {:test} Test65() {
testDeserialiseWithAllElements();
}

// REPEAT 9 - TIME: 34.6639448 s

method {:test} Test66() {
testSerializeWithASingleLeaf();
}
method {:test} Test67() {
testSerializeNullValues();
}
method {:test} Test68() {
testSerializeWithAllElements();
}
method {:test} Test69() {
testDeseraliseWithASingleLeaf();
}
method {:test} Test70() {
testDeserializeWithASingleNode();
}
method {:test} Test71() {
testDeserialiseWithAllElements();
}

// REPEAT 10 - TIME: 37.7882469 s
