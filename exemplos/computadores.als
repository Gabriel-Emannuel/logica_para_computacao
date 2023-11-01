// Conjuntos

abstract sig Computador{}

sig Rapido, BoaMemoria, Compacto in Computador{}

one sig Lenovo, Dell, Apple, Acer extends Computador{}

// Predicados

pred ideal[c: Computador] {
   ehCompacto[c] and temMemoriaBoa[c] and ehCompacto[c]
}

pred temQualidade[c: Computador] {
   ehCompacto[c] or temMemoriaBoa[c] or ehCompacto[c]
}

pred ehRapido[c: Computador] {
    c in Rapido
}

pred temMemoriaBoa[c: Computador] {
    c in BoaMemoria
}

pred ehCompacto[c: Computador] {
    c in Compacto
}

// Restrições

fact {
    one c: Computador | ideal[c]
    all c: Computador | temQualidade[c]

    #Rapido=3 and #BoaMemoria=2 and #Compacto=1

    temMemoriaBoa[Lenovo] <=> temMemoriaBoa[Dell]

    ehRapido[Dell] <=> ehRapido[Apple]

    (ehRapido[Apple] => not ehRapido[Acer]) and (ehRapido[Acer] => not ehRapido[Apple])
}

run {}