// Tipos

sig Usuario {
    perfis_ativos: set Perfil,
    perfis_inativos: set Perfil
}

sig Perfil {
    amigos: set Perfil,
    publicacoes: set Publicacao
}

sig Publicacao{
    conteudo: one Conteudo
}

sig Conteudo{

}

// Predicados


pred eh_ativo_usuario(u:Usuario) {
    one p: Perfil | p in Usuario.perfis_ativos
}

pred eh_amigo(x, y: Perfil) {
    x in y.amigos
}

pred eh_de[perfil: Perfil, publicacao: Publicacao] {
    publicacao in perfil.publicacoes
}

// Restrições

fact {
    all u: Usuario | no (u.perfis_ativos & u.perfis_inativos)
    all u, v: Usuario | no (u.perfis_ativos & v.perfis_inativos)
}

fact {
    all p: Perfil | one u:Usuario | (p in u.perfis_ativos) or (p in u.perfis_inativos)
}

fact { 
    all p: Perfil | not eh_amigo[p, p]
    all x, y: Perfil | eh_amigo[x,y] <=> eh_amigo[y,x]
}

fact {
    all c: Conteudo | one p: Publicacao | 
    c in p.conteudo
}

fact {
    all a: Publicacao | all b: Perfil | all c: Usuario | 
    a in b.publicacoes => b in c.perfis_ativos
}

// Assert

// Run

run {one p: Publicacao | one x, y: Perfil | eh_de[x,p] and eh_de[y,p]}