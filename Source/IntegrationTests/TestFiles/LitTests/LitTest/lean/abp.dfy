
// dafny 4.10.1.0
// Command Line Options:
// generatedOutput

// LIBRARY

datatype Link = Link(src: MachineID, dst: MachineID)

datatype Channel = Channel(msgs: seq<Event>) {
  predicate empty() {|msgs| == 0}
  predicate nonempty() {!empty()}
  predicate init() {empty()}
  static function New(): Channel ensures New().init() { Channel(msgs := [])}

  function length(): nat { |this.msgs| }
  function send(msg: Event): Channel {this.(msgs := msgs + [msg])}
  function receive(): (Event, Channel) requires nonempty() {(msgs[0], this.(msgs := msgs[1..]))}
  function drop(idx: nat): Channel {if idx < |msgs| then this.(msgs := msgs[..idx] + msgs[idx+1..]) else this}
}

datatype Network = Network(channel: map<Link, Channel>) {
  predicate init() {forall link <- channel :: channel[link].init()}
  static function New(): Network ensures New().init() {Network.Network(channel := map[])}

  function length (src: MachineID, dst: MachineID): nat
  {
    if Link(src, dst) in channel then channel[Link(src, dst)].length() else 0
  }

  predicate receivable (src: MachineID, dst: MachineID)
  {
    var link := Link(src, dst);
    link in channel && channel[link].nonempty()
  }

  function peek (src: MachineID, dst: MachineID): Event
    requires receivable(src, dst)
  {
    channel[Link(src, dst)].msgs[0]
  }

  function ensure(link: Link): (res: Network)
    ensures link in res.channel
    ensures link in channel ==> res.channel[link] == channel[link]
    ensures link !in channel ==> res.channel[link].empty()
  {
    if link in channel then this else this.(channel := channel[link := Channel.New()])
  }

  function send(src: MachineID, msg: Event, dst: MachineID): Network
  {
    var link := Link(src, dst);
    this.(channel := channel[link := ensure(link).channel[link].send(msg)])
  }

  function receive(src: MachineID, dst: MachineID): (Event, Network)
    requires receivable(src, dst)
  {
    var link := Link(src, dst);
    var (msg, ch) := channel[link].receive();
    (msg, this.(channel := channel[link := ch]))
  }
}

datatype tData = New(value: nat, bit: bool)

datatype tAck = New(bit: bool)

datatype tSenderInit = New(receiver: ReceiverID, messages: seq<nat>, bit: bool)

datatype tReceiverInit = New(sender: SenderID, bit: bool)

datatype tSenderState = New(messages: seq<nat>, current: nat, bit: bool)

datatype tReceiverState = New(messages: seq<nat>, bit: bool)

datatype Event = Null(Null: ()) | halt(Null: ()) | eData(TData: tData) | eAck(TAck: tAck) | eTick(Null: ()) | eSenderInit(TSenderInit: tSenderInit) | eReceiverInit(TReceiverInit: tReceiverInit) | eSenderState(TSenderState: tSenderState) | eReceiverState(TReceiverState: tReceiverState)

datatype MachineID = Ticker(ticker: TickerID) | Sender(sender: SenderID) | Receiver(receiver: ReceiverID)

datatype Machine = Ticker(ticker: Ticker) | Sender(sender: Sender) | Receiver(receiver: Receiver)

datatype Message = New(target: MachineID, event: Event)

datatype Handler = Return(state: Machine) | Send(message: Message, state: Machine) | Broadcast(messages: seq<Message>, state: Machine)

type TickerID = nat

datatype TickerState = Dummy

datatype Ticker = New(state: TickerState)

type SenderID = nat

datatype SenderState = Init | Sending

datatype Sender = New(receiver: ReceiverID, messages: seq<nat>, current: nat, bit: bool, state: SenderState) {
  function Init_on_eSenderInit(init: tSenderInit): Handler
    requires state.Init?
  {
    Handler.Return(Machine.Sender(this.(receiver := init.receiver).(messages := init.messages).(current := 0).(bit := init.bit).(state := SenderState.Sending())))
  }

  function Sending_on_eAck(ack: tAck): Handler
    requires state.Sending?
  {
    if this.bit == ack.bit then
      Handler.Return(Machine.Sender(this.(current := this.current + 1).(bit := !this.(current := this.current + 1).bit)))
    else
      Handler.Return(Machine.Sender(this))
  }

  function Sending_on_eTick(): Handler
    requires state.Sending?
  {
    if this.current < |this.messages| then
      Handler.Send(Message.New(MachineID.Receiver(this.receiver), Event.eData(tData.New(this.messages[this.current], this.bit))), Machine.Sender(this))
    else
      Handler.Return(Machine.Sender(this))
  }
}

type ReceiverID = nat

datatype ReceiverState = Init | Receiving

datatype Receiver = New(sender: SenderID, messages: seq<nat>, bit: bool, state: ReceiverState) {
  function Init_on_eReceiverInit(init: tReceiverInit): Handler
    requires state.Init?
  {
    Handler.Return(Machine.Receiver(this.(sender := init.sender).(messages := []).(bit := init.bit).(state := ReceiverState.Receiving())))
  }

  function Receiving_on_eData(msg: tData): Handler
    requires state.Receiving?
  {
    if this.bit != msg.bit then
      Handler.Return(Machine.Receiver(this.(messages := this.messages + [msg.value]).(bit := msg.bit)))
    else
      Handler.Return(Machine.Receiver(this))
  }

  function Receiving_on_eTick(): Handler
    requires state.Receiving?
  {
    Handler.Send(Message.New(MachineID.Sender(this.sender), Event.eAck(tAck.New(this.bit))), Machine.Receiver(this))
  }
}

datatype System = New(machines: map<MachineID, Machine>, network: Network) {
  function deliver_eSenderInit_to_Sender_in_Init(src: MachineID, dst: MachineID): System
    requires
      && src in machines
      && dst in machines
      && network.receivable(src, dst)
      && network.receive(src, dst).0.eSenderInit?
      && machines[dst].Sender?
      && machines[dst].sender.state.Init?
  {
    var (event, network') := network.receive(src, dst);
    match machines[dst].sender.Init_on_eSenderInit(event.TSenderInit)
    case Return(state) => this.(machines := machines[dst := state], network := network')
    case Send(msg, state) => this.(machines := machines[dst := state], network := network'.send(dst, msg.event, msg.target))
  }

  function deliver_eAck_to_Sender_in_Sending(src: MachineID, dst: MachineID): System
    requires
      && src in machines
      && dst in machines
      && network.receivable(src, dst)
      && network.receive(src, dst).0.eAck?
      && machines[dst].Sender?
      && machines[dst].sender.state.Sending?
  {
    var (event, network') := network.receive(src, dst);
    match machines[dst].sender.Sending_on_eAck(event.TAck)
    case Return(state) => this.(machines := machines[dst := state], network := network')
    case Send(msg, state) => this.(machines := machines[dst := state], network := network'.send(dst, msg.event, msg.target))
  }

  function deliver_eTick_to_Sender_in_Sending(src: MachineID, dst: MachineID): System
    requires
      && src in machines
      && dst in machines
      && network.receivable(src, dst)
      && network.receive(src, dst).0.eTick?
      && machines[dst].Sender?
      && machines[dst].sender.state.Sending?
  {
    var (event, network') := network.receive(src, dst);
    match machines[dst].sender.Sending_on_eTick()
    case Return(state) => this.(machines := machines[dst := state], network := network')
    case Send(msg, state) => this.(machines := machines[dst := state], network := network'.send(dst, msg.event, msg.target))
  }

  function deliver_eReceiverInit_to_Receiver_in_Init(src: MachineID, dst: MachineID): System
    requires
      && src in machines
      && dst in machines
      && network.receivable(src, dst)
      && network.receive(src, dst).0.eReceiverInit?
      && machines[dst].Receiver?
      && machines[dst].receiver.state.Init?
  {
    var (event, network') := network.receive(src, dst);
    match machines[dst].receiver.Init_on_eReceiverInit(event.TReceiverInit)
    case Return(state) => this.(machines := machines[dst := state], network := network')
    case Send(msg, state) => this.(machines := machines[dst := state], network := network'.send(dst, msg.event, msg.target))
  }

  function deliver_eData_to_Receiver_in_Receiving(src: MachineID, dst: MachineID): System
    requires
      && src in machines
      && dst in machines
      && network.receivable(src, dst)
      && network.receive(src, dst).0.eData?
      && machines[dst].Receiver?
      && machines[dst].receiver.state.Receiving?
  {
    var (event, network') := network.receive(src, dst);
    match machines[dst].receiver.Receiving_on_eData(event.TData)
    case Return(state) => this.(machines := machines[dst := state], network := network')
    case Send(msg, state) => this.(machines := machines[dst := state], network := network'.send(dst, msg.event, msg.target))
  }

  function deliver_eTick_to_Receiver_in_Receiving(src: MachineID, dst: MachineID): System
    requires
      && src in machines
      && dst in machines
      && network.receivable(src, dst)
      && network.peek(src, dst).eTick?
      && machines[dst].Receiver?
      && machines[dst].receiver.state.Receiving?
  {
    var (event, network') := network.receive(src, dst);
    match machines[dst].receiver.Receiving_on_eTick()
    case Return(state) => this.(machines := machines[dst := state], network := network')
    case Send(msg, state) => this.(machines := machines[dst := state], network := network'.send(dst, msg.event, msg.target))
  }

  function deliver(src: MachineID, dst: MachineID): System
    requires
      && src in machines
      && dst in machines
      && network.receivable(src, dst)
  {
    match machines[dst] {
      case Sender(sender) =>
        match sender.state {
          case Init =>
            match network.peek(src, dst) {
              case eSenderInit(_) => deliver_eSenderInit_to_Sender_in_Init(src, dst)
              case _ => this
            }
          case Sending =>
            match network.peek(src, dst) {
              case eAck(_) => deliver_eAck_to_Sender_in_Sending(src, dst)
              case eTick(_) => deliver_eTick_to_Sender_in_Sending(src, dst)
              case _ => this
            }
        }
      case Receiver(receiver) =>
        match receiver.state {
          case Init =>
            match network.peek(src, dst) {
              case eReceiverInit(_) => deliver_eReceiverInit_to_Receiver_in_Init(src, dst)
              case _ => this
            }
          case Receiving =>
            match network.peek(src, dst) {
              case eData(_) => deliver_eData_to_Receiver_in_Receiving(src, dst)
              case eTick(_) => deliver_eTick_to_Receiver_in_Receiving(src, dst)
              case _ => this
            }
        }
      case _ => this
    }
  }

}