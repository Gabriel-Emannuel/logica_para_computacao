// Tipos

abstract sig Amizade {
    amigo: one Perfil,
    de: one Perfil
}

sig AmizadeAtual, AmizadeApagada extends Amizade{}

sig Conteudo{}

sig Historico {
    amizades: set Amizade
}

sig MidiaSocial{
    usuarios: set Usuario,
    historico: one Historico
}

abstract sig Perfil {
    amigos: set Perfil,
    publicacoes: set Publicacao
}

sig PerfilAtivo, PerfilInativo extends Perfil{}

sig Publicacao{
    autor: one Perfil,
    conteudo: one Conteudo
}

abstract sig Usuario {
    perfis: set Perfil
}

sig UsuarioAtivo, UsuarioInativo extends Usuario{}

---

// Fatos de conexão

fact { // Históricos precisam estar ligado a apenas uma mídia.
    all hist: Historico | one midia: MidiaSocial |
    hist = midia.historico
}

fact { // Amizades precisam ser ligadas a apenas um histórico.
    all amizade: Amizade | one historico: Historico |
    amizade in historico.amizades
}

fact { // Usuários precisam estar ligados a apenas uma mídia.
    all usuario_midia: Usuario | one midia: MidiaSocial |
    usuario_midia in midia.usuarios
}

fact { // Perfis precisam estar ligados a apenas um usuário.
    all perfil: Perfil | one user: Usuario |
    perfil in user.perfis
}

fact { // Publicações estão ligadas a pelo menos um perfil.
    all publicacao: Publicacao | some perfil: Perfil |
    publicacao in perfil.publicacoes
}

fact { // Conteúdos de publicação estão ligadas a apenas uma publicação.
    all conteudo_publicacao: Conteudo | one publicacao: Publicacao |
    conteudo_publicacao = publicacao.conteudo
}

---

// fatos de atividade de perfil

pred eh_autor_de_algo[perfil: Perfil] {
    some publicacao: Publicacao |
    perfil = publicacao.autor
}

fact { // Todo perfil ativo é autor de alguma publicação.
    all perfil_ativo: PerfilAtivo |
    eh_autor_de_algo[perfil_ativo]
}

fact { // Todo perfil inativo não é autor de nenhuma publicação.
    all perfil_inativo: PerfilInativo |
    not eh_autor_de_algo[perfil_inativo]
}

fact { // Toda publicação só vai existir em apenas um perfil.
    all publicacao: Publicacao | one perfil: Perfil |
    publicacao in perfil.publicacoes
}

---

// Fatos de atividade de Usuário

pred nao_eh_ativo_usuario[usuario: Usuario] {
    all perfil_ativo: PerfilAtivo |
    not perfil_ativo in usuario.perfis
}

fact { // Um usuário inativo não é ativo.
    all usuario_inativo: UsuarioInativo |
    nao_eh_ativo_usuario[usuario_inativo]
}

---

// Fatos sobre amizade

pred eh_amigo[perfil_1, perfil_2 : Perfil] {
    perfil_1 in perfil_2.amigos
}

pred amizade_contem[amizade: Amizade, perfil_1, perfil_2 : Perfil] {
    (amizade.amigo = perfil_1 and amizade.de = perfil_2) 
    or (amizade.amigo = perfil_2 and amizade.de = perfil_1)
}

fact { // Nenhum perfil pode ser amigo dele mesmo.
    all perfil: Perfil |
    not eh_amigo[perfil, perfil]
}

fact { // Um perfil só pode ser amigo de outro, se este outro também for amigo dele.
    all perfil_1, perfil_2: Perfil | 
    eh_amigo[perfil_1, perfil_2] <=> eh_amigo[perfil_2, perfil_1]
}

fact { // Amizades atuais só existem caso os dois perfis sejam amigos.
    all amizade_atual: AmizadeAtual | all perfil_1, perfil_2: Perfil |
    amizade_contem[amizade_atual, perfil_1, perfil_2] 
    => eh_amigo[perfil_1, perfil_2]
}

fact { // Não pode existir amizades apagadas em que um usuário era amigo dele mesmo.
    all amizade_apagada: AmizadeApagada |
    amizade_apagada.amigo != amizade_apagada.de
}

fact { // Uma amizade apagada só existe se ambos os perfis não são amigos
    all amizade_apagada: AmizadeApagada | all perfil_1, perfil_2: Perfil |
    amizade_contem[amizade_apagada, perfil_1, perfil_2] 
    => not eh_amigo[perfil_1, perfil_2]
}

fact { // Se duas amizades contém os mesmos perfis, então são as mesmas amizades.
    all amizade_1, amizade_2: Amizade | all perfil_1, perfil_2: Perfil |
    (
        amizade_contem[amizade_1, perfil_1, perfil_2] 
        and amizade_contem[amizade_2, perfil_1, perfil_2]
    ) => amizade_1 = amizade_2
}

---
// Asserts e checks

assert user_with_more_than_one_profile {
    some u: Usuario | one p1: Perfil | one p2: Perfil | 
    p1 not = p2 and p1 in u.perfis and p2 in u.perfis and #MidiaSocial=1
}

check user_with_more_than_one_profile {}

---

run {#MidiaSocial=1}
