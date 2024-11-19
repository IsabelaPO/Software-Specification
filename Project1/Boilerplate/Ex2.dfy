method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
  requires arr.Length > 0
  ensures b == true ==> forall x,y:: 0 <= x < arr.Length && 0 <= y < arr.Length && x != y ==> arr[x] != arr[y]
  ensures b == false ==> exists x,y:: 0 <= x < arr.Length && 0 <= y < arr.Length && x != y && arr[x] == arr[y]
 {
  var i := 0; 
  b := true; 

  while (i < arr.Length) 
  decreases arr.Length - i
  invariant 0 <= i <= arr.Length
  invariant b == true ==> forall x,y:: 0 <= x < i && 0 <= y < i && x != y ==> arr[x] != arr[y]
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length)
    decreases arr.Length - j
    invariant 0 <= j <= arr.Length
    invariant b == true ==> forall x,y:: 0 <= x < i && 0 <= y < i && x != y ==> arr[x] != arr[y] 
    invariant b == true ==> forall x:: 0 <= x < j && x != i ==> arr[x] != v 
    {
      var u := arr[j]; 
      if ((j != i) && (u == v)) {
        b := false; 
        return; 
      }
      j := j+1;
    }
    i := i+1; 
  }
}


method noRepetitionsLinear(arr: array<nat>) returns (b: bool)
  requires arr.Length > 0
  ensures b == true ==> forall x, y :: 0 <= x < arr.Length && 0 <= y < arr.Length && x != y ==> arr[x] != arr[y]
  ensures b == false ==> exists x, y :: 0 <= x < arr.Length && 0 <= y < arr.Length && arr[x] == arr[y]
{
  b := true;
  var i := 0;

  var seen := new bool[arr.Length];  

  while (i < arr.Length)
    decreases arr.Length - i
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> seen[arr[k] % arr.Length]
    invariant b == true ==> forall x, y :: 0 <= x < i && 0 <= y < i && x != y ==> arr[x] != arr[y]
  {
    var v := arr[i] % arr.Length;  

    if seen[v] {
      b := false;
      return;
    }

    seen[v] := true;

    i := i + 1;
  }
}







