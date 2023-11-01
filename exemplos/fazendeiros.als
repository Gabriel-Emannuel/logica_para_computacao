abstract sig Fazendeiros{}

sig donoMula in Fazendeiros{}

one sig A, B, C extends Fazendeiros{}

pred ehDono[f: Fazendeiros] {
    f in donoMula
}

fact {
    
    one f: Fazendeiros | ehDono[f]

    (ehDono[C] and ehDono[A]) or (not ehDono[C] and not ehDono[A])

    (not ehDono[C] and not ehDono[A]) or (ehDono[C] and ehDono[A])

    (ehDono[C] and not ehDono[A]) or (not ehDono[C] and ehDono[A])
}

run{}