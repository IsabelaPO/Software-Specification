
module Ex3 {

  class Node {

    var val : nat
    var next : Node?

    ghost var footprint : set<Node>
    ghost var content : set<nat> 

    ghost function Valid() : bool 
      reads this, this.footprint 
      decreases footprint
    {
      this in this.footprint 
      &&
      if (this.next == null)
        then 
          this.footprint == { this }
          && 
          this.content == { this.val }
        else 
          this.next in this.footprint
          &&
          this !in this.next.footprint
          &&      
          this.footprint == { this } + this.next.footprint 
          &&
          this.content == { this.val } + this.next.content
          &&
          this.next.Valid()
    }

    constructor (v : nat) 
    ensures this.Valid()
    ensures this.val == v
    ensures this.footprint == {this}
    ensures this.content == {this.val}
    {
      this.val := v;
      this.next := null;
      this.footprint := {this};
      this.content := {v};
    }

    method add(v : nat) returns (r : Node)
    requires Valid()
    ensures Valid() && r.Valid()
    ensures r.next == this
    ensures r.val == v
    ensures r.footprint == {r} + this.footprint
    ensures r.content == {v} + old(this.content)
    {
      r := new Node(v);
      r.val := v;
      r.next := this;
      r.footprint := { r } + this.footprint;
      r.content := { r.val } + this.content;
    }


    method mem(v : nat) returns (b : bool)
    requires Valid()
    ensures b == (v in this.content)
    decreases footprint
    {
      if(this.val==v){
        b:=true;
      }
      else
      {
        if(this.next == null){
          b:=false;
          return;
        }
        else
        {
          b := this.next.mem(v);
        }
      }
    }

    method copy() returns (n : Node)
    requires Valid()
    ensures n.Valid() && Valid()
    ensures fresh(n.footprint)
    ensures n.content == this.content
    decreases footprint
    {
      n := new Node(this.val);
      if(this.next != null) 
      {
        var n_next := this.next.copy();
        n.next := n_next;
        n.footprint := { n } + n_next.footprint;
        n.content := { n.val } + n_next.content;
      }
    }

  }
  
}
