include "Ex3.dfy"

module Ex4 {
  import Ex3=Ex3

  class Set {
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, footprint, this.list
    {
      if (this.list == null)
        then 
          footprint == {}
          &&
          content == {}
        else 
          footprint == list.footprint
          &&
          content == list.content
          &&
          list.Valid()
    }

    constructor () 
      ensures Valid() && this.content == {} && this.footprint == {}
    {
      list := null; 
      footprint := {}; 
      content := {};      
    }


    method mem (v : nat) returns (b : bool)
    requires Valid()
    ensures b == (v in this.content)
    decreases footprint
    {
      if(this.list == null)
      {
        b := false;
      }
      else {
        b := this.list.mem(v);
      }
    }

    method add (v : nat) 
    requires Valid()
    ensures this.Valid()
    ensures this.content == {v} + old(this.content)
    modifies this
    {
      var newNode := new Ex3.Node(v);
      newNode.val := v;
      newNode.next := this.list; 
      this.list := newNode; 
      newNode.footprint := {newNode} + this.footprint;
      newNode.content := {v} + this.content;
      this.footprint := newNode.footprint;
      this.content := newNode.content;
    }

    method union(s : Set) returns (r : Set)
      requires Valid() && s.Valid()
      ensures r.Valid()
      ensures r.content == this.content + s.content 
    {
      r := new Set();
      
      var current := this.list; 
     
      if(current != null){
        while (current != null)
        invariant r.Valid()
        invariant current != null ==> current.Valid()
        invariant current != null ==> this.content == r.content + current.content
        invariant current == null ==> this.content == r.content
        invariant this.content == {} ==> r.content == {}
        decreases if current == null then 0 else |current.footprint|
        {
          var valor := r.mem(current.val);
          if (!(valor)){
            r.add(current.val);
            current := current.next;
          }
          else {
            current := current.next;
          }
        }
      }

      var otherCurrent := s.list;
      if(otherCurrent != null){
        while (otherCurrent != null)
        invariant r.Valid()
        invariant otherCurrent != null ==> otherCurrent.Valid()
        invariant otherCurrent != null ==> s.content + this.content == r.content + otherCurrent.content
        invariant otherCurrent == null ==> s.content + this.content == r.content
        invariant this.content == {} && s.content == {} ==> r.content == {}
        invariant s.content == {} ==> r.content == this.content
        decreases if otherCurrent == null then 0 else |otherCurrent.footprint|
        {
           var valor := r.mem(otherCurrent.val);
          if (!(valor)){
            r.add(otherCurrent.val);
            otherCurrent := otherCurrent.next;
          }
          else {
            otherCurrent := otherCurrent.next;
          }
        }
      }
    }


    method inter(s: Set) returns (r: Set)
      requires Valid() && s.Valid()
      ensures r.Valid()
      ensures r.content == this.content * s.content
    {
      r := new Set();
      var thisList := this.list;
      if(thisList != null){
        while (thisList != null)
          invariant r.Valid()
          invariant thisList != null ==> thisList.Valid()
          invariant thisList != null ==> r.content + (thisList.content * s.content) == this.content * s.content
          invariant thisList == null ==> r.content == this.content * s.content
          invariant forall x :: x in r.content ==> x in this.content && x in s.content
          decreases if thisList == null then 0 else |thisList.footprint|
        {
          var valor1 := s.mem(thisList.val);
          var valor2 := r.mem(thisList.val);
          if (valor1 && !valor2) {
            r.add(thisList.val);
          }
          thisList := thisList.next;
        }
      }
    }

  }

}

