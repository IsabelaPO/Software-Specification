sig Node {
  outbox: set Msg
}

sig Member in Node { 
 nxt: one Node, 
 qnxt : Node -> lone Node 
}

one sig Leader in Member {
   lnxt: Member -> lone Member
}

sig LQueue in Member {}

sig Msg {
  sndr: Node, 
  rcvrs: set Node 
}

sig SentMsg, SendingMsg, PendingMsg in Msg {}

fun queuers[m : Member] : set Node {
  m.^(~(m.qnxt))
}


fact TopologicalConstraints
{
	///only one ring
    	all m: Member | m.^nxt=Member
	
	//non-member nodes are not allowed to queue in more than one member queue at a time
	all n: Node, m1,m2: Member | 
		(n->m1) in m1.qnxt and (n->m2) in m2.qnxt
		implies m1=m2

	//each member queue consists of a (possibly empty) list of non-member nodes ending in the member in charge of that queue
	all n: (Node-Member) | some (n.(Member.qnxt)) implies 
		some m: Member | n in queuers[m]
	//only one arrow pointing to Member
	all m: Member | lone m.~(m.qnxt)
	//only one arrow leaving node 
	all n: Node - Member | lone n.(Member.qnxt)
	//no arrow leaving Member
	no Member.(Member.qnxt) 
	
	//the leader queue consists of a list of member nodes ending in the leader
	all l: Leader, m: Member | some (m.(Leader.lnxt)) implies m in l.^(~(l.lnxt))
	//Leader not in LQueue
	no (Leader & LQueue) 
	//only one arrow pointing to leader
	lone Leader.~(Leader.lnxt) 
	//no arrow leaving Leader
	no Leader.(Leader.lnxt)
	//only one arrow pointing to Member or none
	all m: Member | lone m.(Leader.lnxt)
       // Lqueue has only members of lnxt
       LQueue = Leader.^(~(Leader.lnxt))

}

fact MessageConsistency
{
	//The outbox can only contain:
	//pending messages belonging to node itself
	all m: Node | all msg: PendingMsg | (msg.sndr = m implies msg in m.outbox )
	//the outbox can only contain sending messages belonging to the current leader
	some m: Member |all msg: SendingMsg| msg in m.outbox implies msg.sndr in Leader
	//If a node has a message in its outbox that belongs to the leader
	//then the node is in the rcvrs: 
	//the node is a member
	all n: Node, msg: SendingMsg | (msg in n.outbox && msg.sndr in Leader) implies n in msg.rcvrs && n in Member
	//If member is a rcvrs, the outbox has message 
	all msg: SendingMsg, m: Member | m in msg.rcvrs implies msg in m.outbox
	//Nodes cannot receive their own messages
	all msg: Msg | msg.sndr !in msg.rcvrs
	
	//Sending Messages:
	//They need to have rcvrs
	all msg: SendingMsg | some msg.rcvrs && msg.rcvrs in Member
	//Must be in someone outbox
	all msg: SendingMsg| msg in Member.outbox
	//Leader is the only sndr of SendingMsg
	all msg: SendingMsg | msg.sndr in Leader

	//Pending Msg:
	//have no rcvrs
	no PendingMsg.rcvrs  
	//is only in the outbox of its sender
	all n: Node, msg: PendingMsg | msg in n.outbox implies msg !in (Node-n).outbox
	
	//Sent Msg: 
	//no outbox
	all msg: SentMsg | msg !in Node.outbox
	//have receivers
	SentMsg.rcvrs in Node 

	//Msg cannot be in the three states at the same time 
	no (PendingMsg & SendingMsg) 
	no (PendingMsg & SentMsg) 
	no (SendingMsg & SentMsg) 
	//Node cannot have msg that are already Sending 
	all msg: Msg| msg in (Node-Member).outbox implies msg !in SendingMsg

}

fun VisualiseLnxt: Member -> Member
{
	Node.lnxt 
}

fun VisualiseQnxt: Node -> Node
{
	Node.qnxt 
}

//run commands

fact {
   some (Node-Member)
}
/*
run {
  some Leader
  some LQueue
  some m1, m2: Member, n1, n2: Node | n1 in queuers[m1] && n2 in queuers[m2] && m1!=m2
  some SentMsg
  some SendingMsg
  some PendingMsg
} for 6 Node, 3 Msg*/

/*
run {
  some Leader
  some LQueue
  some m1, m2: Member, n1, n2: Node | n1 in queuers[m1] && n2 in queuers[m2] && m1!=m2
  some SentMsg
  some SendingMsg
  some PendingMsg
} for 5 Node, 3 Msg*/




