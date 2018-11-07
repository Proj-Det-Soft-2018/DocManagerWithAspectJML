package purchase.model;

import java.util.ArrayList;
import java.util.List;

import business.model.Situation;

public enum PurchaseSituation implements Situation {
  /*   / ENUM NAME /DESCRIPTION                               /LINKED NODES*/
  /* 0*/ NULL      (null,                                     new int[]{0, 1}),
  /* 1*/ AGCHLOCAL ("Aguardando autorização da chefia local", new int[]{1, 2}),
  /* 2*/ AGAUTCOMP ("Aguardando autorização para compra",	  new int[]{1, 2, 3}),
  /* 3*/ ANSETORCA ("Em análise no setor de orçamento",       new int[]{2, 3, 4, 11}),
  /* 4*/ EMPENHADO ("Empenhado",                              new int[]{3, 4, 5}),
  /* 5*/ NOTFORNEC ("Notificado para o fornecedor",           new int[]{4, 5, 6, 10}),
  /* 6*/ APRFORNEC ("Aprovado pelo fornecedor",               new int[]{5, 6, 7, 10}),
  /* 7*/ ENVFORNEC ("Enviado pelo fornecedor",                new int[]{6, 7, 8, 10}),
  /* 8*/ RECEBALMX ("Recebido pelo almoxarifado",             new int[]{7, 8, 9, 10}),
  /* 9*/ PAGOLIQUD ("Pago/Liquidado",                         new int[]{8, 9}),
  /*10*/ FORAPRAZO ("Não entregue dentro do prazo",           new int[]{5, 6, 7, 8, 10, 12}),
  /*11*/ AUDITORIA ("Em auditoria",                           new int[]{3, 11, 12}),
  /*12*/ SJURIDICO ("Em análise pelo setor jurídico",         new int[]{10, 11, 12, 13}),
  /*13*/ CANCELADO ("Cancelado",                              new int[]{12, 13});
	
	private String description;

	  private int[] linkedNodesIndexes;

	  PurchaseSituation(String description, int[] neighborNodes){
	    this.description = description;
	    this.linkedNodesIndexes = neighborNodes;
	  }

	  public static List<Situation> getAll() {
	    List<Situation> situationList = new ArrayList<>();
	    for(PurchaseSituation situation : PurchaseSituation.values()) {
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

	  public static PurchaseSituation getSituationById(int id){
	    return PurchaseSituation.values()[id];
	  }
}
