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

assert historico_depende_de_midia_social {
    one hist: Historico | all midia: MidiaSocial | hist != midia.historico
}

assert amizade_not_self_loop {
    all a: Amizade | a.amigo != a.de
}

assert perfil_ativo_usuario_ativo {
    all p:PerfilAtivo | one u:UsuarioAtivo | p in u.perfis
}

assert perfil_inativo_usuario_inativo {
    all p:PerfilInativo | one u:UsuarioInativo | p in u.perfis
}

assert perfil_usuario {
    all p: Perfil | one u: Usuario | p in u.perfis
}

assert conteudo_to_publicacao{
    all c: Conteudo | some p: Publicacao | p.conteudo = c
}

assert user_mais_de_um_perfil {
    lone u: Usuario | one p1: Perfil | one p2: Perfil | 
    p1 not = p2 and p1 in u.perfis and p2 in u.perfis
}

check historico_depende_de_midia_social {}
check amizade_not_self_loop {}
check perfil_ativo_usuario_ativo {}
check perfil_inativo_usuario_inativo {}
check perfil_usuario {}
check conteudo_to_publicacao {}
check user_mais_de_um_perfil {}
---
run {#MidiaSocial=1}
=======

<<<<<<< HEAD
// Asserts e checks

assert user_with_more_than_one_profile {
    some u: Usuario | one p1: Perfil | one p2: Perfil | 
    p1 not = p2 and p1 in u.perfis and p2 in u.perfis and #MidiaSocial=1
}

check user_with_more_than_one_profile {}

---

run {#MidiaSocial=1}
=======
// fatos para quaisquer mídia social ser independente e não ter conexões entre sí

fact {
    all perfil_1, perfil_2 : Perfil | one usuario_1, usuario_2: Usuario | one midia: MidiaSocial |
    
    // se perfil_1 e perfil_2 serem amigos e serem de usuários diferentes, então esses usuários são da mesma mídia social
    (
        eh_amigo[perfil_1, perfil_2] and (
            usuario_1 != usuario_2 => (
                perfil_1 in usuario_1.perfis 
                and perfil_2 in usuario_2.perfis
            ) 
        )
    ) => (
        (usuario_1 + usuario_2) in midia.usuarios
    )
}

fact {
    all amizade: Amizade | all perfil_1, perfil_2: Perfil | one usuario_1, usuario_2: Usuario | one midia: MidiaSocial |

    (
        amizade_contem[amizade, perfil_1, perfil_2] and (
            usuario_1 != usuario_2 => (
                perfil_1 in usuario_1.perfis
                and perfil_2 in usuario_2.perfis
            )
        )
    ) => (
        (usuario_1 + usuario_2) in midia.usuarios
    )
}
run { #MidiaSocial=1}
>>>>>>> 972e609e666bfb28516b9a2856d89d28afa1063a
>>>>>>> 9c734c92b96ab9170526204401b7754370d698c1
