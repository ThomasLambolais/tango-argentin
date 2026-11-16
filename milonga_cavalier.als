// Milonga du point de vue d'un cavalier : modele Alloy 6 temporel
// Hypothese pedagogique : une tanda comporte ici exactement quatre morceaux.
// Les volontes et signaux exterieurs ne sont PAS commandes par le cavalier.
module milonga_cavalier
open util/ordering[Piece] as songOrder

sig Guest {}
sig Lane {}
sig Piece {}

abstract sig Phase {}
one sig Seated, Seeking, Offered, Ready,
        Dancing, Escorting, Chatting extends Phase {}

abstract sig Signal {}
one sig MusicOn, CortinaOn, MusicalCue extends Signal {}

one sig Ball {
  var phase: one Phase,
  var partner: lone Guest,
  var piece: one Piece,
  var lane: lone Lane
}

// Signatures variables : choix et conditions du monde exterieur.
var sig EyeContact in Guest {}   // mirada reciproque observee
var sig Consent in Guest {}      // accord libre et revisable
var sig ClearLane in Lane {}     // intervalle de securite dans la ronda
var sig Heard in Signal {}      // tanda en cours, repere musical
var sig OnFloor in Guest {}     // partenaire effectivement sur piste

fact FourSongs { #Piece = 4 }
fact ExclusiveMusic { always (CortinaOn in Heard implies MusicOn not in Heard) }

fact Initial {
  Ball.phase = Seated
  no Ball.partner
  Ball.piece = songOrder/first
  no Ball.lane
}

fact WellFormed {
  always {
    (Ball.phase in Seated + Seeking + Chatting) implies no Ball.partner
    (Ball.phase in Offered + Ready + Dancing + Escorting)
      implies one Ball.partner
    (Ball.phase = Dancing) implies {
      OnFloor = Ball.partner
      one Ball.lane
      Ball.partner in Consent
      MusicOn in Heard
    }
    (Ball.phase != Dancing) implies no OnFloor
    (Ball.phase != Dancing) implies no Ball.lane
    (Ball.phase = Ready) implies Ball.partner in Consent
  }
}

// Les predicats ci-dessous ne modifient que l'etat interne du cavalier.
// EyeContact, Consent, ClearLane et Heard evoluent librement : environnement.
pred pause {
  Ball.phase' = Ball.phase
  Ball.partner' = Ball.partner
  Ball.piece' = Ball.piece
  Ball.lane' = Ball.lane
}
pred seek {
  Ball.phase in Seated + Chatting
  Ball.phase' = Seeking
  no Ball.partner'
  Ball.piece' = songOrder/first
  no Ball.lane'
}
pred cabeceo[g: Guest] {
  Ball.phase = Seeking
  g in EyeContact
  Ball.phase' = Offered
  Ball.partner' = g
  Ball.piece' = Ball.piece
  no Ball.lane'
}
pred decline {
  Ball.phase = Offered
  Ball.partner not in Consent'
  Ball.phase' = Seeking
  no Ball.partner'
  Ball.piece' = Ball.piece
  no Ball.lane'
}
pred accept {
  Ball.phase = Offered
  Ball.partner in Consent'
  Ball.phase' = Ready
  Ball.partner' = Ball.partner
  Ball.piece' = Ball.piece
  no Ball.lane'
}
pred cancelBeforeEntry {
  Ball.phase = Ready
  Ball.partner not in Consent'
  Ball.phase' = Seeking
  no Ball.partner'
  Ball.piece' = Ball.piece
  no Ball.lane'
}
pred enter[l: Lane] {
  Ball.phase = Ready
  l in ClearLane
  MusicOn in Heard'
  Ball.partner in Consent'
  Ball.phase' = Dancing
  Ball.partner' = Ball.partner
  Ball.piece' = songOrder/first
  Ball.lane' = l
}
pred musicalStep {
  Ball.phase = Dancing
  Ball.piece != songOrder/last
  Ball.lane in ClearLane
  MusicalCue in Heard
  Ball.partner in Consent'
  Ball.phase' = Dancing
  Ball.partner' = Ball.partner
  Ball.piece' = Ball.piece.(songOrder/next)
  Ball.lane' = Ball.lane
}
pred completeTanda {
  Ball.phase = Dancing
  Ball.piece = songOrder/last
  CortinaOn in Heard'
  Ball.phase' = Escorting
  Ball.partner' = Ball.partner
  Ball.piece' = Ball.piece
  no Ball.lane'
}
pred emergencyStop {
  Ball.phase = Dancing
  Ball.partner not in Consent'
  Ball.phase' = Escorting
  Ball.partner' = Ball.partner
  Ball.piece' = Ball.piece
  no Ball.lane'
}
pred escortBack {
  Ball.phase = Escorting
  Ball.phase' = Chatting
  no Ball.partner'
  Ball.piece' = Ball.piece
  no Ball.lane'
}

fact Dynamics {
  always {
    pause or seek or decline or accept or cancelBeforeEntry
    or musicalStep or completeTanda or emergencyStop or escortBack
    or (some g: Guest | cabeceo[g])
    or (some l: Lane | enter[l])
  }
}

// Proprietes de surete : des obligations, non des objectifs de vivacite.
assert NoDanceWithoutConsent {
  always (Ball.phase = Dancing implies Ball.partner in Consent)
}
assert NoLaneJump {
  always ((Ball.phase = Dancing and Ball.phase' = Dancing)
          implies Ball.lane' = Ball.lane)
}
assert MusicalProgress {
  always ((Ball.phase = Dancing and Ball.phase' = Dancing
           and Ball.piece != Ball.piece')
          implies (MusicalCue in Heard and Ball.lane in ClearLane))
}
assert ReturnFollowsExit {
  always (Ball.phase = Chatting implies once (Ball.phase = Escorting))
}

// Le run cherche une trace temoin : rien ne garantit automatiquement
// qu'une invitation soit acceptee ou qu'une tanda arrive a son terme.
pred RepeatAfterConversation {
  eventually (Ball.phase = Chatting and
    after eventually (Ball.phase = Seeking and
      after eventually (Ball.phase = Dancing)))
}
// Scenario plus exigeant : une tanda normale est achevee (cortina),
// le cavalier revient discuter, puis cherche et danse de nouveau.
pred FullTandaThenRepeat {
  eventually (completeTanda and
    after eventually (Ball.phase = Chatting and
      after eventually (Ball.phase = Seeking and
        after eventually (Ball.phase = Dancing))))
}
run FullTandaThenRepeat for 6 but exactly 3 Guest,
  exactly 2 Lane, exactly 4 Piece, 22 steps
run RepeatAfterConversation for 6 but exactly 3 Guest,
  exactly 2 Lane, exactly 4 Piece, 22 steps
check NoDanceWithoutConsent for 6 but exactly 3 Guest,
  exactly 2 Lane, exactly 4 Piece, 16 steps
check NoLaneJump for 6 but exactly 3 Guest,
  exactly 2 Lane, exactly 4 Piece, 16 steps
check MusicalProgress for 6 but exactly 3 Guest,
  exactly 2 Lane, exactly 4 Piece, 16 steps
check ReturnFollowsExit for 6 but exactly 3 Guest,
  exactly 2 Lane, exactly 4 Piece, 16 steps
