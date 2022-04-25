type Opaque
type OpaqueT(==) = Opaque // Error: Opaque doesn't support ==

datatype Datatype = DT(t: Opaque)
type DatatypeT(==) = Datatype // Error: Opaque doesn't support ==

type Synonym = Opaque
type SynonymT(==) = Synonym // Error: Opaque doesn't support ==

type Subset = t: Opaque | true witness *
type SubsetT(==) = Subset // Error: Opaque doesn't support ==

datatype Ghost = G(ghost i: int)
type GhostT(==) = Ghost // Error: `i` is ghost

datatype ThroughArg = C(s: Ghost)
type ThroughArgT(==) = ThroughArg // Error: Ghost doesn't support ==
