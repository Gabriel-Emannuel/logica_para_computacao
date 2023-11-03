// Tipos

sig Amizade {
    perfil_1: one Perfil,
    perfil_2: one Perfil
}

sig Conteudo{

}

sig Historico {
    amizades_apagadas: set Amizade,
    amizades_atual: set Amizade
}

sig MidiaSocial{
    usuarios: set Usuario,
    historico: one Historico
}

sig Perfil {
    publicacoes: set Publicacao
}

sig Publicacao{
    autor: one Perfil,
    conteudo: one Conteudo
}

sig Usuario {
    perfis_ativos: set Perfil,
    perfis_inativos: set Perfil
}

// Predicados

pred eh_amizade_atual[amizade: Amizade] {
    one historico: Historico |
    amizade in historico.amizades_atual
}

pred eh_amigo[p1, p2: Perfil] {
    one amizade: Amizade |
    eh_amizade_atual[amizade] and (
    (amizade.perfil_1 = p1 and amizade.perfil_2 = p2) or 
    (amizade.perfil_2 = p1 and amizade.perfil_1 = p2))
}

pred eh_ativo_usuario(u:Usuario) {
    one p: Perfil | p in Usuario.perfis_ativos
}

pred eh_de[perfil: Perfil, publicacao: Publicacao] {
    publicacao in perfil.publicacoes
}

pred eh_amizade_semelhante[a1, a2: Amizade] {
    ((a1.perfil_1 = a2.perfil_1) and (a1.perfil_2 = a2.perfil_2)) or
    ((a1.perfil_2 = a2.perfil_1) and (a1.perfil_1 = a2.perfil_2)) 
}

// Restrições

fact {
    #MidiaSocial=1
}

fact {
    all usuario: Usuario | one midia: MidiaSocial |
    usuario in midia.usuarios
}

fact {
    all historico: Historico |
    no (historico.amizades_atual & historico.amizades_apagadas)
}

fact {
    all perfil: Perfil | one amigo: Perfil| all publicacao: Publicacao |
    (publicacao in perfil.publicacoes) => 
    ((publicacao.autor = perfil) or (publicacao.autor = amigo and eh_amigo[amigo, perfil]))
}

fact {
    all hist: Historico | one midia: MidiaSocial |
    hist = midia.historico
}

fact {
    all amizade: Amizade | one historico: Historico |
    (amizade in historico.amizades_apagadas) or (amizade in historico.amizades_atual)
}

fact {
    all a1, a2: Amizade |
    (a1 != a2) => not eh_amizade_semelhante[a1, a2]
}

fact {
    all amizade: Amizade |
    amizade.perfil_1 != amizade.perfil_2
}

fact {
    all u: Usuario | no (u.perfis_ativos & u.perfis_inativos)
    all u, v: Usuario | no (u.perfis_ativos & v.perfis_inativos)
}

fact {
    all p: Perfil | one u:Usuario | (p in u.perfis_ativos) or (p in u.perfis_inativos)
}

fact {
    all publi: Publicacao | one perfil: Perfil | 
    publi in perfil.publicacoes
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

run {#Amizade=3}