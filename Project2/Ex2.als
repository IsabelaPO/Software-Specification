sig Node {
  var outbox: set Msg
}

var sig Member in Node { 
 var nxt: one Node, 
 var qnxt : Node -> lone Node 
}

var one sig Leader in Member {
   var lnxt: Member -> lone Member
}

var sig LQueue in Member {}

sig Msg {
  sndr: Node, 
  var rcvrs: set Node 
}

var sig SentMsg, SendingMsg, PendingMsg in Msg {}


pred init
{
	one Leader 
	no LQueue
       all msg: Msg | msg in PendingMsg
	all msg: PendingMsg | msg in msg.sndr.outbox
	all n: Node, msg: PendingMsg | msg in n.outbox implies msg.sndr = n
	no Msg.rcvrs
	no SentMsg
	no SendingMsg
       nxt = Leader->Leader
       no qnxt 
       no lnxt
}



pred stutterMsg[] {
  outbox' = outbox
  rcvrs' = rcvrs 
  PendingMsg' = PendingMsg
  SendingMsg' = SendingMsg
  SentMsg' = SentMsg
}

pred stutterRing[] {
  Member' = Member
  nxt' = nxt
}

pred stutterLeader[] {
  Leader' = Leader
  LQueue' = LQueue
  lnxt' = lnxt
}

pred stutterQueues[] {
  qnxt' = qnxt
}


pred stutter[] 
{
  stutterMsg[]
  stutterRing[]
  stutterLeader[]
  stutterQueues[]
}


pred trans[]
{
	stutter[]
       or 
	(some m: Member, n: Node | MemberApplication[m,n])
	or
	(some m: Member, n: Node | MemberPromotion[m,n])
	or
	(some l: Leader, m: Member | LeaderApplication[l,m])
	or 
	(some l: Leader, m: Member | LeaderPromotion[l,m])
	or 
	(some m,m1: Member| MemberExit[m,m1])
	or
	(some m: Member, n: Node | NonMemberExit[m,n])
	or 
	(some l: Leader, m: Member, msg: Msg | BroadcastInitialisation[l,m,msg])
	or 
	(some m1, m2: Member, msg: Msg | MessageRedirect[m1,m2,msg])
	or 
	(some l: Leader, m: Member, msg: Msg | BroadcastTermination[l,m,msg])
}


pred system[] {
  init[] 
  always trans[]
}


fun queuers[m : Member] : set Node {
  m.^(~(m.qnxt))
}

pred MemberApplication[m: Member, n: Node]
{
	some n2: Node | MemberApplicationAux2[m, n, n2] 
	or 
	MemberApplicationAux1[m, n]
}

pred MemberApplicationAux1[m: Member, n: Node]
{
	//Precondition
	//Member queue is empty
	no m.~(m.qnxt)
	//Node not in any Member queue
       no n.(Member.qnxt)
	//n is not a Member
       n !in Member

	//Post
	//n is added to empty member queue
	m.qnxt' = (n->m)
	//rest of member queues remain the same 
       all m1 : Member-m | m1.qnxt' = m1.qnxt 

	//frame
	//Msg does not change
	stutterMsg[]
	//Ring does not change
       stutterRing[]
	//Leader does not change
       stutterLeader[]
}


pred MemberApplicationAux2[m: Member, n: Node, n_last: Node]
{
	//pre-condition 
	//Member queue not empy
	some m.~(m.qnxt)
	//Node not in any Member queue	
	no n.(Member.qnxt)
	//n is not a Member
	n !in Member
	//node is in the member queue
	n_last in queuers[m]
	//node is the last in the queue
	no n_last.~(m.qnxt)

	//Post
	//n is inserted into the member queue
	m.qnxt' = m.qnxt + (n->n_last) 
	//rest of member queues remain the same 
        all m1 : Member-m | m1.qnxt' = m1.qnxt 

	//frame
	//Msg does not change
	stutterMsg[]
	//Ring does not change
       stutterRing[]
	//Leader does not change
       stutterLeader[]
}

pred MemberPromotion[m: Member, n: Node]
{
	MemberPromotion1[m,n]
	or 
	some n1: Node | 	MemberPromotion2[m,n,n1]
}

pred MemberPromotion1[m: Member, n: Node]
{
	//PreCondition
	//node is in member queue
	n in queuers[m]
	//n is not a member
	n !in Member
	//n is the last in the queue
	no n.~(m.qnxt)
	//n is after m
	n = m.~(m.qnxt)
	
	//PostConditions
	//member queue is empty
	m.qnxt' = m.qnxt - (n->m)
	n.qnxt' = n.qnxt - n.qnxt
	//rest of member queues are the same 
	all m1 : Member'-m | m1.qnxt' = m1.qnxt
	//n is now a member
	Member' = Member + n 
	//n is part of the ring 
	m.nxt' = n && n.nxt' = m.nxt
	//rest of ring is the same 
	all otherM: Member-(m + n) | otherM.nxt' = otherM.nxt

	//Frame 
	//Msg does not change
	stutterMsg[]
	//Leader does not change
       stutterLeader[]
}

pred MemberPromotion2[m: Member, n: Node, n_next: Node]
{
	//PreCondition
	//node is in member queue
	n in queuers[m]
	n_next in queuers[m]
	//n is not a member
	n !in Member
	n_next !in Member
	//n_next is after n
	n_next = n.~(m.qnxt)
	//n is after m
	n = m.~(m.qnxt)
	
	//PostConditions
	//member queue is updated
	m.qnxt' = m.qnxt + (n_next->m) - ((n->m) + (n_next->n)) 
	//rest of member queues are the same 
	all m1 : Member'-m | m1.qnxt' = m1.qnxt 
	//n is now a Member 
	Member' = Member + n
	//n is part of the ring 
	nxt' = (nxt - (m->m.nxt)) + (m->n) + (n->m.nxt)
	//rest of ring is the same 
	//all otherM: Member'-m| otherM.nxt' = otherM.nxt

	//Frame 
	//Msg does not change
	stutterMsg[]
	//Leader does not change
       stutterLeader[]
}

pred LeaderApplication[l: Leader, m: Member]
{
	LeaderApplication1[l,m]
	or
	some m1: Member | LeaderApplication2[l,m,m1]
}

pred LeaderApplication1[l: Leader, m: Member]
{
	//PreCondition
	//Leader queue is empty
	no l.~(l.lnxt)
	//Member not in LQueue
	m !in LQueue
	//no LQueue
	no LQueue
	//member not a Leader
	m !in Leader

	//PostCondition
	//new Leader Queue
	LQueue' = LQueue + m
	//Leader remains the same 
	Leader' = Leader
	//Add m to the leader queue
	l.lnxt' = l.lnxt + (m->l)
	//rest of list remains the same
	all l1: Leader' - l | l1.lnxt' = l1.lnxt

	//Frame 
	//Msg does not change
	stutterMsg[]
	//Ring does not change
       stutterRing[]
	//Member does not change
       stutterQueues[]
}

pred LeaderApplication2[l: Leader, m: Member, m_next: Member]
{
	//PreCondition
	//Leader queue is not empty
	some l.~(l.lnxt)
	//Member not in LQueue
	m !in LQueue
	//Leader not in LQueue
	l !in LQueue
	//m_next in LQueue
	m_next in LQueue
	//m_next is the last member
	no m_next.~(l.lnxt)
	//member not a Leader
	m !in Leader

	//PostCondition
	//new Leader Queue
	LQueue' = LQueue + m
	//Leader remains the same 
	Leader' = Leader
	//Add m to the leader queue
	l.lnxt' = l.lnxt + (m->m_next) 
	//rest of list remains the same
	all l1: Leader' - l | l1.lnxt' = l1.lnxt

	//Frame 
	//Msg does not change
	stutterMsg[]
	//Ring does not change
       stutterRing[]
	//Member does not change
       stutterQueues[]
}

pred LeaderPromotion[l: Leader, m: Member]
{
	LeaderPromotion1[l,m]
	or 
	some m1: Member | LeaderPromotion2[l,m,m1]
}

pred LeaderPromotion1[l: Leader, m: Member]
{
	//Pred
	//m is the only in LQueue
	no m.~(l.lnxt)
	//Member is in LQueue
	m in LQueue
	//m is not a Leader 
	m !in Leader
	//l is a Leader
	l in Leader
	//Leader not in LQueue
	l !in LQueue
	//m is first in line
	m = l.~(l.lnxt)
	//No ongoing Msg
	no SendingMsg 
	
	//Post
	//update LQueue
	l.lnxt' = l.lnxt - (m->l)
	//remove m from LQueue
	LQueue' = LQueue - m
	//Update new Leader
	Leader' = Leader - l + m
	//rest of LQueue remains the same 
	all lq: LQueue' | lq' = lq
	//rest of list remains the same
	all l1: Leader' | l1.lnxt' = l1.lnxt
	
	//Frame
	//Msg does not change
	stutterMsg[]
	//Ring does not change
       stutterRing[]
	//Member does not change
       stutterQueues[]
}

pred LeaderPromotion2[l: Leader, m: Member, m_next: Member]
{
	//Pred
	//Members are in LQueue
	m in LQueue
	m_next in LQueue
	//m_next is after m in LQueue
	m_next = m.~(l.lnxt)
	//l is a leader
	l in Leader
	l !in LQueue
	//m is first in line
	m = l.~(l.lnxt)
	//No ongoing Msg
	no SendingMsg 
	
	//Post
	//update LQueue
	m.lnxt' = l.lnxt - (m->l)
	//remove new leader from LQueue
	LQueue' = LQueue - m
	//Update new Leader
	Leader' = Leader - l + m
	//rest of LQueue remains the same 
	all lq: LQueue - m  | lq' = lq
	//rest of list remains the same
	all l1: Leader - l| l1.lnxt' = l1.lnxt
	
	
	//Frame
	//Msg does not change
	stutterMsg[]
	//Ring does not change
       stutterRing[]
	//Member does not change
       stutterQueues[]
}

pred MemberExit[m: Member, m1: Member]
{
	MemberExit1[m,m1]
	or 
	some n: Node | MemberExit2[m,m1,n]
	or 
	some n,n2: Node | MemberExit3[m,m1,n,n2]

}

pred MemberExit1[m: Member, m_next: Member]
{
	//PreCondition
	//m is not a leader
	m !in Leader 
	//m is after m_ next in ring
	m_next = m.~(nxt)
	//no member queue
	no queuers[m]
	//no Msg to send 
	no outbox

	//postConditon
	//update Ring
	m_next.nxt' = m.nxt
	//update Member set
	Member' = Member - m 
	//rest of ring remains the same
	all m1: Member' - m_next | m1.nxt' = m1.nxt
	
	//Frame
	//Msg does not change
	stutterMsg[]
	//Member does not change
       stutterQueues[]
	//Leader does not change
       stutterLeader[]
}

pred MemberExit2[m: Member, m_next: Member, first_n: Node]
{
	//PreCondition
	//m is not a leader
	m !in Leader
	//m is after m_ next in ring
	m_next = m.~(nxt)
	//some nodes in member queue
	some queuers[m]
	// first node is the first in the m queue
	first_n = m.~(m.qnxt)
	//no member queue in other member 
	no m_next.qnxt
	//no Msg to send 
	no outbox //se tiver

	//postConditon
	//update Ring
	m_next.nxt' = m.nxt
	//update Member set
	Member' = Member - m 
	//rest of ring remains the same
	all m1: Member' - m_next | m1.nxt' = m1.nxt
	//add nodes to other member queue
	m_next.qnxt' = m_next.qnxt + m.qnxt + (first_n -> m_next) - (first_n -> m)
	//update new qnxt
	m.qnxt' = m.qnxt - m.qnxt
	//rest of Member queue remains the same
	all m1: Member' - m_next | m1.qnxt' = m1.qnxt
	
	//Frame
	//Msg does not change
	stutterMsg[]
	//Leader does not change
       stutterLeader[]
}

pred MemberExit3[m: Member, m_next: Member, first_n: Node, last_n: Node]
{
	//PreCondition
	//m is not a leader
	m !in Leader
	//m is after m_ next in ring
	m_next = m.~(nxt)
	//some nodes in member queue
	some queuers[m]
	// first node is the first in the m queue
	first_n = m.~(m.qnxt)
	//member queue in other member 
	some queuers[m_next]
	//last_n in queuers of m_next
	last_n in queuers[m_next]
	//last node of member queue
	no last_n.~(m_next.qnxt)
	//no Msg to send 
	no outbox 

	//postConditon
	//update Ring
	m_next.nxt' = m.nxt
	//update Member set
	Member' = Member - m 
	//rest of ring remains the same
	all m1: Member' - m_next | m1.nxt' = m1.nxt
	//add nodes to other member queue
	m_next.qnxt' = m_next.qnxt + (m.qnxt - (first_n -> m)) + (first_n -> last_n) 
	//update new qnxt
	m.qnxt' = m.qnxt - m.qnxt
	//rest of Member queue remains the same
	all m1: Member' - m_next | m1.qnxt' = m1.qnxt
	
	//Frame
	//Msg does not change
	stutterMsg[]
	//Leader does not change
       stutterLeader[]
}

pred NonMemberExit[m: Member, n: Node]
{
	NonMemberExit1[m,n]
	or 
	some n2: Node | NonMemberExit2[m,n,n2]
}

pred NonMemberExit1[m: Member, n: Node]
{
	//PreConditions
	//n in member queue
	n in queuers[m]
	//n is the last node in queue 
	no n.~(m.qnxt)
	//Node is not a member
	n !in Member
	
	//PostConditions 
	//update member queue
	m.qnxt' = m.qnxt - (n->m)
	//rest of member queues remain the same 
	all m1: Member - m | m1.qnxt' = m1.qnxt

	//Frame 
	//Msg does not change
	stutterMsg[]
	//Ring does not change
       stutterRing[]
	//Leader does not change
       stutterLeader[]
}

pred NonMemberExit2[m: Member, n: Node, n_next: Node]
{
	//PreConditions
	//nodes in member queue
	n in queuers[m]
	n_next in queuers[m]
	//n_ next is after n in queue 
	n_next = n.~(m.qnxt)
	//Nodes are not a member
	n !in Member
	n_next !in Member
	
	//PostConditions 
	//update member queue
	m.qnxt' = m.qnxt - (n->n.(m.qnxt)) - (n_next->n) + (n_next->n.(m.qnxt))
	//rest of member queues remain the same 
	all m1: Member - m | m1.qnxt' = m1.qnxt

	//Frame 
	//Msg does not change
	stutterMsg[]
	//Ring does not change
       stutterRing[]
	//Leader does not change
       stutterLeader[]
}

pred BroadcastInitialisation[l: Leader, m: Member, msg: Msg]
{
	//PreCondition
	//leader outbox must have message
	msg in l.outbox
	//msg cannot be anywhere else 
	msg !in (Node-l).outbox
	//Member must be next of Leader 
	m = l.nxt
	//msg must be in Pending State
	msg in PendingMsg
	msg !in SendingMsg
	msg !in SentMsg
	
	//PostCondition
	//update member outbox
	m.outbox' = m.outbox + msg
	//keep leader outbox
	l.outbox' = l.outbox - msg
	//outbox is the same in the rest
	all m: Node' - (m + l)| m.outbox' = m.outbox
	//update sndr
	msg.sndr' = l 
	//update rcvrs
	msg.rcvrs' = msg.rcvrs + m
	//rest of messages remain the same 
	all msg1: Msg - msg| msg1.sndr' = msg1.sndr
	all msg1: Msg - msg| msg1.rcvrs' = msg1.rcvrs
	
	//update Msg state
	SendingMsg' = SendingMsg + msg
	PendingMsg' = PendingMsg - msg
	SentMsg' = SentMsg
	
	
	//Frame
	//Ring does not change
       stutterRing[]
	//Leader does not change
       stutterLeader[]
	//Member does not change
       stutterQueues[]
}

pred MessageRedirect[m1: Member, m2: Member, msg: Msg]
{
	//PreConditions
	//m1 and m2 must be members
	m1 !in Leader
	m2 !in Leader
	//the message must come from the Leader
	msg.sndr in Leader
	//Msg received by  m1 and not to m2 
	m1 in msg.rcvrs 
	m2 !in msg.rcvrs
	//Msg in m1 outbox and not in m2 
	msg in m1.outbox 
	msg !in m2.outbox
	//Msg is in Sending state
	msg in SendingMsg

	//PostConditions
	//update member outbox
	m1.outbox' = m1.outbox - msg
	m2.outbox' = m2.outbox + msg
	//rest remain the same
	all m: Node' - (m1+m2) | m.outbox' = m.outbox
	//add m2 to receivers 
	msg.rcvrs' = msg.rcvrs + m2
	//rest of messages remain the same 
	all msg1: Msg - msg| msg1.sndr' = msg1.sndr
	all msg1: Msg - msg| msg1.rcvrs' = msg1.rcvrs
	//Msg state remains the same 
	SendingMsg' = SendingMsg 
	PendingMsg' = PendingMsg
	SentMsg' = SentMsg

	//Frame 
	//Ring does not change
       stutterRing[]
	//Leader does not change
       stutterLeader[]
	//Member does not change
       stutterQueues[]
	
	
}

pred BroadcastTermination[l: Leader, m: Member, msg: Msg]
{
	//Pre
	//message already sent to every member
	l.^(nxt)-l = msg.rcvrs
	//message is in Sending state
	msg in SendingMsg
	//the sender is the leader
	msg.sndr = l
	//the member is not a Leader
	m != Leader
	//the message is in the outbox of the member
	msg in m.outbox
	//member already received message
	m in msg.rcvrs

	//Post
	//remove from all next outbox 
	(Member-Leader).outbox' = (Member-Leader).outbox - msg
	//rest remain the same
	all m1: Node' - Member'| m1.outbox' = m1.outbox
	//messages remain the same
	msg.rcvrs' = msg.rcvrs
	//update Msg state
	SendingMsg' = SendingMsg - msg
	PendingMsg' = PendingMsg
	SentMsg' = SentMsg + msg

	//Frame 
	//Ring does not change
       stutterRing[]
	//Leader does not change
       stutterLeader[]
	//Member does not change
       stutterQueues[]
	
}

fun visualizeQueues[] : Node->lone Node {
  Member.qnxt
}

fun VisualiseLnxt: Member -> Member
{
	Node.lnxt 
}

fact {system[] }
/*
run { (eventually some l: Leader, m: Member | LeaderPromotion[l,m])
	&&
	(eventually some m,m1: Member| MemberExit[m,m1])
	&&
	(eventually some m: Member, n: Node | NonMemberExit[m,n])
	&& (eventually some l: Leader, m: Member, msg: Msg | BroadcastTermination[l,m,msg])} for 7 Node, 1 Msg*/

run { (eventually some l: Leader, m: Member | LeaderPromotion[l,m])
	&&
	(eventually some m,m1: Member| MemberExit[m,m1])
	&&
	(eventually some m: Member, n: Node | NonMemberExit[m,n])
	&& (eventually some l: Leader, m: Member, msg: Msg | BroadcastTermination[l,m,msg])} for 8 Node, 1 Msg


