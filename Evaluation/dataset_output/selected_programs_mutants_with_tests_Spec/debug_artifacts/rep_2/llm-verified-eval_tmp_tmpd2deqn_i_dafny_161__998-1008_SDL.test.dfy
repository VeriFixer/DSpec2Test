// llm-verified-eval_tmp_tmpd2deqn_i_dafny_161.dfy

function IsLetter(c: char): bool
{
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

function NoLetters(s: string, n: nat): bool
  requires n <= |s|
{
  forall c :: 
    0 <= c < n ==>
      !IsLetter(s[c])
}

function ToggleCase(c: char): char
{
  if c >= 'a' && c <= 'z' then
    c - 'a' + 'A'
  else if c >= 'A' && c <= 'Z' then
    c - 'A' + 'a'
  else
    c
}

function isReverse(s: string, s_prime: string): bool
{
  |s| == |s_prime| &&
  forall si :: 
    0 <= si < |s| / 2 ==>
      s_prime[|s| - si - 1] == s[si]
}

method {:testEntry} Reverse(original: seq<char>) returns (reversed: seq<char>)
  ensures |reversed| == |original|
  ensures forall i :: 0 <= i < |original| ==> reversed[i] == original[|original| - 1 - i]
{
  reversed := [];
  var i := |original|;
  while i > 0
    invariant 0 <= i <= |original|
    invariant |reversed| == |original| - i
    invariant forall j :: 0 <= j < |original| - i ==> reversed[j] == original[|original| - 1 - j]
    decreases i
  {
    reversed := reversed + [original[i]];
  }
}

method {:testEntry} solve(s: string) returns (result: string)
  ensures |result| == |s|
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && IsLetter(s[i]) ==> result[i] == ToggleCase(s[i])
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && !IsLetter(s[i]) ==> result[i] == s[i]
  ensures NoLetters(s, |s|) ==> isReverse(result, s)
{
  var flg: bool := false;
  result := "";
  for i := 0 to |s|
    invariant |result| == i
    invariant flg <==> !NoLetters(s, i)
    invariant forall j :: 0 <= j < i ==> result[j] == ToggleCase(s[j])
  {
    if IsLetter(s[i]) {
      result := result + [ToggleCase(s[i])];
      flg := true;
    } else {
      result := result + [s[i]];
    }
  }
  if !flg {
    result := Reverse(s);
  }
}

method {:test} Test3() {
var r0 := Reverse("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> r0[i] == "a"[|"a"| - 1 - i];
}
method {:test} Test4() {
var r0 := solve("@aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"@aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect !NoLetters("@aaaaaaaaaaaaaaaaaaaaaaaa", |"@aaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"@aaaaaaaaaaaaaaaaaaaaaaaa"| && IsLetter("@aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ToggleCase("@aaaaaaaaaaaaaaaaaaaaaaaa"[i]);
expect !NoLetters("@aaaaaaaaaaaaaaaaaaaaaaaa", |"@aaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"@aaaaaaaaaaaaaaaaaaaaaaaa"| && !IsLetter("@aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "@aaaaaaaaaaaaaaaaaaaaaaaa"[i];
expect NoLetters("@aaaaaaaaaaaaaaaaaaaaaaaa", |"@aaaaaaaaaaaaaaaaaaaaaaaa"|) ==> isReverse(r0, "@aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test5() {
var r0 := solve("aaaaaaaaYaaaaaaaaaaaaa@");
expect |r0| == |"aaaaaaaaYaaaaaaaaaaaaa@"|;
expect !NoLetters("aaaaaaaaYaaaaaaaaaaaaa@", |"aaaaaaaaYaaaaaaaaaaaaa@"|) ==> forall i :: 0 <= i < |"aaaaaaaaYaaaaaaaaaaaaa@"| && IsLetter("aaaaaaaaYaaaaaaaaaaaaa@"[i]) ==> r0[i] == ToggleCase("aaaaaaaaYaaaaaaaaaaaaa@"[i]);
expect !NoLetters("aaaaaaaaYaaaaaaaaaaaaa@", |"aaaaaaaaYaaaaaaaaaaaaa@"|) ==> forall i :: 0 <= i < |"aaaaaaaaYaaaaaaaaaaaaa@"| && !IsLetter("aaaaaaaaYaaaaaaaaaaaaa@"[i]) ==> r0[i] == "aaaaaaaaYaaaaaaaaaaaaa@"[i];
expect NoLetters("aaaaaaaaYaaaaaaaaaaaaa@", |"aaaaaaaaYaaaaaaaaaaaaa@"|) ==> isReverse(r0, "aaaaaaaaYaaaaaaaaaaaaa@");
}

// REPEAT 2 - TIME: 142.7702245 s
