package juridical.model;

import java.util.ArrayList;
import java.util.List;

import business.model.Situation;

public enum JuridicalSituation implements Situation {
	/*   / ENUM NAME 				/DESCRIPTION                              				 /LINKED NODES*/
	/* 0*/ NULL      			(null,                                     	new int[]{0, 1}),
	/* 1*/ PETICAO      		("Petição Inicial!",                       	new int[]{1, 2}),
	/* 2*/ NOMEACAO   			("Nomeação de Inventariante",               new int[]{2, 3}),
	/* 3*/ COMPROMISSO  		("Inventariante Presta Compromisso",        new int[]{2, 3, 4}),
	/* 4*/ DECLARACOES1  		("Primeiras Declarações",                 	new int[]{3, 4, 5, 6}),
	/* 5*/ APURACAO  			("Apuração de Bens",                      	new int[]{4, 5}),
	/* 6*/ CITACAO 				("Citação de Interessados",                	new int[]{4, 6, 7, 8, 9, 11}),
	/* 7*/ ARQUICAO 			("Arquição de erros e omissões",            new int[]{6, 7, 10}),
	/* 8*/ ALTHERDEIRO 			("Solicitação de Mudança de Herdeiro",      new int[]{6, 8, 10}),
	/* 9*/ RECNOMINVENTARIANTE  ("Reclamação de Nomeação de Inventariante", new int[]{6, 9, 10}),
	/*10*/ APRECIACAOJUIZ 		("Apreciação pelo Juiz",   					new int[]{1, 7, 8, 9, 10, 11, 14}),
	/*11*/ AVBENS 				("Avaliação de Bens",                  		new int[]{8, 10, 11, 12, 13}),
	/*12*/ CRITICA 				("Crítica das Partes",     					new int[]{10, 11, 12}),
	/*13*/ ACEITE 				("Aceite das Partes",       				new int[]{11, 13, 14}),
	/*14*/ DECLARACOESULT 		("Ultimas Declarações",            			new int[]{13, 14, 15}),
	/*15*/ PARTILHA  			("Partilha de Bens",  						new int[]{14, 15, 16}),
	/*16*/ CONCLUIDO 			("Concluido",                              	new int[]{15, 16});

	private String description;

	private int[] linkedNodesIndexes;


	JuridicalSituation(String description, int[] neighborNodes){
		this.description = description;
		this.linkedNodesIndexes = neighborNodes;
	}

	public static List<Situation> getAll() {
		List<Situation> situationList = new ArrayList<>();
		for(JuridicalSituation situation : JuridicalSituation.values()) {
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

	public static JuridicalSituation getSituationById(int id){
		return JuridicalSituation.values()[id];
	}

}
