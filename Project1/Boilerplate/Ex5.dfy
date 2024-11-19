include "Ex3.dfy"

module Ex5 {
  import Ex3=Ex3

  class Set {
    var tbl : array<bool>  
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

     ghost function Valid() : bool 
      reads this, footprint, this.list, this.tbl 
    {
      if (this.list == null) 
      then 
        footprint == {}
        && 
        content == {}
        &&
        (forall i :: 0 <= i < tbl.Length ==> tbl[i] == false)
      else 
        footprint == list.footprint 
        &&
        content == list.content 
        &&
        (forall i :: 0 <= i < tbl.Length ==> tbl[i]== (i in content)) 
        &&
        (forall v :: v in this.content ==> 0 <= v < tbl.Length)
        &&
        list.Valid()    
        }

method VerifyAllFalse(tbl: array<bool>)
    requires tbl != null
    requires tbl.Length >= 0
    ensures (forall i :: 0 <= i < tbl.Length ==> tbl[i] == false)
    modifies tbl
{
    var i := 0;
    while i < tbl.Length
        invariant 0 <= i <= tbl.Length
        invariant (forall j :: 0 <= j < i ==> tbl[j] == false)
    {
        tbl[i] := false;
        i := i + 1;
    }
}

constructor (size: nat)
    requires size >= 0
    ensures Valid() && this.content == {} && this.footprint == {}
    ensures fresh(tbl)
    ensures tbl.Length == size
    {
        this.list := null;
        this.footprint := {};
        this.content := {};
        this.tbl := new bool[size];

        new;
        
        VerifyAllFalse(this.tbl);
    }


    method mem (v : nat) returns (b : bool)
     requires 0 <= v < tbl.Length
     requires Valid()
     ensures b == this.tbl[v]
    {
      b := tbl[v]; 
    }


method add(v : nat) 
    requires Valid()
    requires 0 <= v < tbl.Length
    ensures Valid()
    ensures old(tbl) == tbl
    ensures tbl[v] == true
    modifies this, tbl
{
    if (!tbl[v]) {
        tbl[v] := true; 
        if (this.list != null) {
            ghost var oldcontent := this.list.content;
            var newNode := this.list.add(v); 
            assert newNode.content == oldcontent + {v};
            this.content :=  newNode.content;
            this.footprint := newNode.footprint;
            this.list := newNode;
        } else {
            this.list := new Ex3.Node(v); 
            this.footprint := {this.list}; 
            this.content := {this.list.val}; 
        }
    }
}

 method union(s : Set) returns (r : Set)
      requires Valid() 
      requires s.Valid()
      ensures r.Valid()
      ensures (forall x:: 0 <= x < tbl.Length && x in r.content && r.tbl[x] == true ==> x in s.content && x in this.content)
      ensures r.content == this.content + s.content
      modifies this
    {
      var maxSize := if this.tbl.Length >= s.tbl.Length then this.tbl.Length else s.tbl.Length;
 
      r := new Set(maxSize);

      var current := this.list; 

      while (current != null)
      invariant r.Valid()
      invariant current != null ==> current.Valid()
      invariant current != null ==> (forall x:: x in current.content ==> x in this.content)
      invariant current != null ==> current.content + r.content == this.content
      invariant current == null ==> this.content == r.content
      invariant (forall v:: v in r.content ==> v < r.tbl.Length)
      invariant this.content == {} ==> r.content == {}
      decreases if current == null then 0 else |current.footprint|
      {
        if(current.val < r.tbl.Length){
          var valor := r.mem(current.val);
          if !(valor)
          {
          r.add(current.val);
          var aux := r.mem(current.val);
          assert aux == true;
          }
        }
        current := current.next;
      }

      var otherCurrent := s.list;

      if(otherCurrent != null){
        while (otherCurrent != null)
          invariant r.Valid()
          invariant otherCurrent != null ==> otherCurrent.Valid()
          invariant otherCurrent != null ==> s.content + this.content == r.content + otherCurrent.content
          invariant otherCurrent == null ==> s.content + this.content == r.content
          invariant (forall v:: v in r.content ==> v < r.tbl.Length)
          invariant this.content == {} && s.content == {} ==> r.content == {}
          invariant s.content == {} ==> r.content == this.content
          decreases if otherCurrent == null then 0 else |otherCurrent.footprint|
          {
            if(otherCurrent.val < r.tbl.Length){
              var valor := r.mem(otherCurrent.val);
              if !(valor)
              {
              r.add(otherCurrent.val);
              var aux := r.mem(otherCurrent.val);
              assert aux == true;
              }
            }
            otherCurrent := otherCurrent.next;
          }
      }
      
      }

    method inter(s : Set) returns (r : Set)
      requires Valid() && s.Valid()
      ensures r.Valid()
      ensures r.content == this.content * s.content
    {
      var minSize := if this.tbl.Length <= s.tbl.Length then this.tbl.Length else s.tbl.Length;

      r := new Set(minSize);

      if minSize == 0 {
        return;
      }

      for i := 0 to minSize - 1 {
        if tbl[i] && s.tbl[i] {
          r.add(i);
        }
      }
    }

  }

}