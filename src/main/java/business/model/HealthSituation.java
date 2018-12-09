package business.model;

import java.util.ArrayList;
import java.util.List;

import business.model.Situation;

public enum HealthSituation implements Situation {
  //ENUM NAME /DESCRIPTION                               /LINKED NODES*/
  NULL       (null,                                     new int[]{0, 1, 13}),
  ANALISE    ("Análise",                                new int[]{1, 2, 3, 12, 14}),
  CONVOCAR   ("A convocar",                             new int[]{1, 14, 2, 4, 6, 7, 9}),
  SOLICDOC   ("Solicitar Documento(s)",                 new int[]{1, 3, 4, 5}),
  SEMEXITO   ("Contato Sem Êxito",                      new int[]{2, 3, 4, 5, 6}),
  AGUARDDOC  ("Aguardando Documento(s)",                new int[]{3, 4, 5, 6, 13}),
  CONVOCADO  ("Convocado",                              new int[]{2, 4, 5, 6, 9, 10, 11}),
  AGUARDEXT  ("Aguardando Perícia Externa",             new int[]{2, 7, 8}),
  AGENDEXT   ("Agendada Perícia Externa",               new int[]{7, 8, 9, 10}),
  ENCEQMULT  ("Encaminhado p/ Eq. Multiprofissional",   new int[]{2, 6, 8, 9, 13}),
  DESPACHAR  ("Pronto para Despachar",                  new int[]{6, 8, 11, 13, 10, 15}),
  PROBSIAPE  ("Aguardando Resolver Problema SIAPE",     new int[]{6, 11, 10, 12}),
  ENCCOVEPS  ("Encaminhado a Coordenação COVEPS",       new int[]{1, 11, 12, 13}),
  AGRDPERIT  ("Aguardando Perito Finalizar",            new int[]{5, 12, 9, 13, 10}),
  INTIMPED   ("Interessado Impedido de Ser Periciado",  new int[]{1, 14, 2}),
  CONCLUIDO  ("Concluido",                              new int[]{10, 15});

  private /*@ spec_public nullable @*/ String description; // in sitDescription;
  //@ protected represents sitDescription <- description;

  private /*@ spec_public @*/ int[] linkedNodesIndexes;

  //@ public invariant 2 <= linkedNodesIndexes.length;

  /*@ requires 0 < neighborNodes.length;
  @ assignable this.description, this.linkedNodesIndexes;
  @ ensures this.linkedNodesIndexes == neighborNodes && this.description == description;
  @*/
  HealthSituation(String description, int[] neighborNodes){
    this.description = description;
    this.linkedNodesIndexes = neighborNodes;
  }

  /*@	ensures \result.size() == 15;
  @		ensures \result.contains(HealthSituation.NULL) == false;
  @*/
  public static List<Situation> getAll() {
    List<Situation> situationList = new ArrayList<>();
    for(HealthSituation situation : HealthSituation.values()) {
      situationList.add(situation);
    }
    situationList.remove(0);
    return situationList;
  }

  @Override
  public String getDescription() {
    return description;
  }

  @Override
  public int getId() {
    return ordinal();
  }

  @Override
  public List<Situation> getlinkedNodes() {
    List<Situation> linkedNodes = new ArrayList<>();
    for(int i: linkedNodesIndexes) {
      linkedNodes.add(getSituationById(i));
    }
    return linkedNodes;
  }

  /*@ requires id >=0 && id < 15;
  @   ensures \result != null;
  @*/
  public static HealthSituation getSituationById(int id){
    return HealthSituation.values()[id];
  }
}
