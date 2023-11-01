// Conjuntos

abstract sig Suspeito{}

sig Culpado in Suspeito{}

one sig Filipe, Romeuette extends Suspeito{}

// Predicados

pred ehCulpado[s: Suspeito] {
    s in Culpado
}

// Restrições

fact {
    not ehCulpado[Filipe]
    ehCulpado[Filipe] => ehCulpado[Romeuette]
}

run{}