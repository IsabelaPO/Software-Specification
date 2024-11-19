datatype uop = Neg 
datatype bop = Plus | Minus 

datatype aexpr =
  Var(seq<nat>)
  | Val(nat)
  | UnOp(uop, aexpr)
  | BinOp(bop, aexpr, aexpr)
 
datatype code = 
  | VarCode(seq<nat>)  
  | ValCode(nat)       
  | UnOpCode(uop)      
  | BinOpCode(bop)     

function Serialize(a : aexpr) : seq<code> 
{
  match a {
    case Var(s) => [ VarCode(s) ]
    case Val(i) => [ ValCode(i) ]
    case UnOp(op, a1) => Serialize(a1) + [ UnOpCode(op) ]
    case BinOp(op, a1, a2) => Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ]
  }
}


/*
  Ex1.1
*/

function DeserializeAux(cs: seq<code>, tree: seq<aexpr>):  seq<aexpr>
decreases cs, tree {
  if (cs == []) 
    then tree
    else DeserializeAux(cs[1..], DeserializeAuxAux(cs[0], tree))
}

function DeserializeAuxAux(cs: code, tree: seq<aexpr>):  seq<aexpr>
{
  match cs {
    case VarCode(s) =>
       [Var(s)] + tree

    case ValCode(i) =>
      [Val(i)] + tree

    case UnOpCode(op) =>
      if |tree| < 1 then [ ]
      else [UnOp(op, tree[0])] + tree[1..]

    case BinOpCode(op) =>
      if |tree| < 2 then [ ]
      else [BinOp(op, tree[0], tree[1])] + tree[2..]
  }
}

function Deserialize(cs: seq<code>) : seq<aexpr>
  decreases cs 
{
  DeserializeAux(cs, [])
}

/*
  Ex1.2
*/
lemma DeserializePropertyAuxLemma(t : aexpr, cds :seq<code>, ts : seq <aexpr>)
ensures DeserializeAux(Serialize(t) + cds, ts) == DeserializeAux(cds, [ t ]+ts) 
{
  match t {
      case Var(s) => 
        calc {
          DeserializeAux(Serialize(t)+cds, ts);
            == 
              DeserializeAux([ VarCode(s) ] + cds, ts);
            == 
              DeserializeAux(cds, DeserializeAuxAux(VarCode(s), ts));
            ==
              DeserializeAux(cds, [ Var(s) ] + ts);
        }
      
      case Val(i) =>
        calc{
          DeserializeAux(Serialize(t)+cds, ts);
            == 
              DeserializeAux([ ValCode(i) ] + cds, ts);
            == 
              DeserializeAux(cds, DeserializeAuxAux(ValCode(i), ts));
            ==
              DeserializeAux(cds, [ Val(i) ] + ts);
        }

      case BinOp(op, t1, t2) =>
        assert Serialize(t2) + Serialize(t1) + [ BinOpCode(op) ] + cds == Serialize(t2) + (Serialize(t1) + [ BinOpCode(op) ] + cds);
        assert Serialize(t1) + [BinOpCode(op)] + cds == Serialize(t1) + ([BinOpCode(op)] + cds); 
        assert  [ t1 ] + ([ t2 ] + ts) == [ t1, t2] + ts;
        calc {
        DeserializeAux(Serialize(t) + cds, ts); 
          ==
            DeserializeAux(Serialize(t2) + Serialize(t1) + [ BinOpCode(op) ] + cds, ts);
          == 
            DeserializeAux(Serialize(t2) + (Serialize(t1) + [ BinOpCode(op) ] + cds), ts);
          == { DeserializePropertyAuxLemma(t2, Serialize(t1) + [ BinOpCode(op) ] + cds, ts); }
            DeserializeAux(Serialize(t1) + [BinOpCode(op)] + cds, [ t2 ] + ts);
          == 
            DeserializeAux(Serialize(t1) + ([BinOpCode(op)] + cds), [ t2 ] + ts);
          == { DeserializePropertyAuxLemma(t1, [ BinOpCode(op) ] + cds, [ t2 ] + ts); }
            DeserializeAux([ BinOpCode(op) ] + cds, [ t1 ] + ([ t2 ] + ts));
          == 
            DeserializeAux([ BinOpCode(op) ] + cds, [ t1, t2] + ts);
          ==
            DeserializeAux(cds, DeserializeAuxAux(BinOpCode(op), [ t1, t2 ] + ts));
          == 
            DeserializeAux(cds, [ BinOp(op,t1, t2) ] + ts); 
          == 
            DeserializeAux(cds, [ t ] + ts);
      }
      case UnOp(op, t1) =>
        assert Serialize(t1) + [UnOpCode(op)] + cds == Serialize(t1) + ([UnOpCode(op)] + cds);
        calc{
           DeserializeAux(Serialize(t) + cds, ts); 
           ==
            DeserializeAux( Serialize(t1) + [ UnOpCode(op) ] + cds, ts);
          ==
            DeserializeAux( Serialize(t1) +( [ UnOpCode(op) ] + cds), ts);
          == { DeserializePropertyAuxLemma(t1, [ UnOpCode(op) ] + cds, ts); }
            DeserializeAux([UnOpCode(op)] + cds, [ t1 ] + ts);
          ==
            DeserializeAux(cds, DeserializeAuxAux(UnOpCode(op), [ t1 ] + ts));
          ==
            DeserializeAux(cds, [ UnOp(op,t1) ] + ts); 
          ==
            DeserializeAux(cds, [ t ] + ts);
        }

    }
}

lemma DeserializeProperty(e : aexpr)
ensures Deserialize(Serialize(e)) == [ e ]
{
  assert Serialize(e) + [] == Serialize(e);
  calc{
    Deserialize(Serialize(e));
    ==
      Deserialize(Serialize(e) + []);
    ==
      DeserializeAux(Serialize(e) + [],[]);
    == { DeserializePropertyAuxLemma(e, [], []); }
      DeserializeAux([],[e]+[]);
    == 
      DeserializeAux([],[e]);
    ==
      [e];
  }
}


/*
  Ex1.3
*/
function SerializeCodes(cs : seq<code>) : seq<nat> 
decreases cs
{
  if |cs| == 0 then [] 
  else 
    var c := cs[0];
    var rest := cs[1..];
    match c {
      case VarCode(s) =>
        var len := |s|;
        var serialize := [0] + [len] + s; // Codificação para VarCode
        serialize + SerializeCodes(rest)

      case ValCode(i) => 
        [1] + [i] + SerializeCodes(rest)  // Codificação para ValCode

      case UnOpCode(op) =>
        [2] + SerializeCodes(rest)

      case BinOpCode(op) =>
        var opCode := match op {
          case Plus => 2  // Codificação para operador binário Plus
          case Minus => 3 // Codificação para operador binário Minus
        };
        [3] + [opCode] + SerializeCodes(rest)
    }

}


function DeserializeCodes(ints : seq<nat>) : seq<code> 
requires |ints| >= 0 
decreases ints {
  if |ints| == 0 
  then 
    []  
  else
    if ints[0] < 0 || ints[0] > 3 
    then
      [] 
    else
      match ints[0] {
        case 0 =>
          if |ints| < 2 
          then [] 
          else 
            var len := ints[1];
            if |ints| < 2 + len 
            then [] 
            else 
              var s := ints[2..2+len];  
              var rest := ints[2+len..];
              [VarCode(s)] + DeserializeCodes(rest)
            
        case 1 =>
          if |ints| < 2 
          then [] 
          else 
            var i := ints[1];
            var rest := ints[2..];  
            [ValCode(i)] + DeserializeCodes(rest)

        case 2 =>
          if |ints| < 1 
          then [] 
          else 
            var rest := ints[1..];
            var op := Neg;
            [UnOpCode(op)] + DeserializeCodes(rest)

        case 3 =>
          if |ints| < 2 
          then [] 
          else 
            var op := if ints[1] == 2 then Plus else Minus;
            var rest := ints[2..];
            [BinOpCode(op)] + DeserializeCodes(rest)
          }  
}




/*
  Ex1.4
*/
lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
}

/*
  Ex1.5
*/
function FullSerialize(e : aexpr) : seq<nat> {
 SerializeCodes(Serialize(e))
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 Deserialize(DeserializeCodes(nats))
}

/*
  Ex1.6
*/
lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
  calc{
    FullDeserealize(FullSerialize(e));
    ==
      Deserialize(DeserializeCodes(SerializeCodes(Serialize(e))));
    == {DeserializeCodesProperty(Serialize(e));}
      Deserialize(Serialize(e));
    == {DeserializeProperty(e);}
      [e];
  }
    
}