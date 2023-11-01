abstract sig Pessoa{}

sig capazesPrenderMoriarty in Pessoa{}

one sig Watson, Holmes extends Pessoa{}

pred ehCapazPrender[p: Pessoa] {
    p in capazesPrenderMoriarty
}

fact {
    all p: Pessoa | ehCapazPrender[Watson] => ehCapazPrender[p]
    not ehCapazPrender[Holmes]
}

run{}