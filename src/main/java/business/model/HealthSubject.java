package business.model;

import java.util.ArrayList;
import java.util.List;

import business.model.Subject;

public enum HealthSubject implements Subject {
	
	NULL("INV","- Inválido -"),
	APO("Aposentadoria","Aposentadoria por Invalidez"),
	PENSAO("Pensão","Avaliação para fins de pensão"),
	REMOCAOFAMILIA("Rem. Família","Remoção por motivo de saúde de pessoa de sua família"),
	REMOCAOPROPRIOSERVIDOR("Rem. Servidor","Remoção por motivo de saúde do servidor"),
	HORARIO_ESPECIAL_FAMILIA("Horário Esp. Família","Horário especial para servidor com familiar com deficiência"),
	HORARIO_ESPECIAL_SERVIDOR("Horário Esp. Servidor","Horário especial para servidor com deficiência"),
	CONSTATACAO_DEFICIENCIA("Constatação Deficiência","Constatação de deficiência dos candidatos aprovados em vaga de pessoa com deficiência"),
	ACIDENTE_SERVICO("Acidente em Serviço","Recomendação para tratamento de acidentados em serviço em instituição " + 
			"privada à conta de recursos públicos"),
	REVERSAO("Reversão Aposentadoria","Avaliação de servidor aposentado por invalidez para fins de reversão"),
	INTEGRALIZACAO("Integralização de Proventos","Avaliação de servidor aposentado para fins de integralização de proventos"),
	DISPONIBILIDADE("Av. Disponibilidade","Avaliação da capacidade laborativa de servidor em disponibilidade"),
	IRPF_APOSENTADORIA("IRPF Aposentadoria","Avaliação para isenção de imposto de renda sobre Aposentadoria"),
	IRPF_PENSAO("IRPF Pensao","Avaliação para isenção de imposto de renda sobre Pensão"),
	AUXILIO_PRE_ESCOLAR("Auxílio Pré Escolar","Avaliação de idade mental de dependente para concessão de auxílio pré-escolar"),
	REGIME_DOMICILIAR("Regime Domiciliar","Avaliação de Regime Domiciliar para Aluno Doente"),
	AV_DEPENDENTE("Av. Dependente","Avaliação de Dependente"),
	AV_SANIDADE_MENTAL("Av. Sanidade Mental PAD",
						"Avaliação de sanidade mental do servidor para fins de Processo Administrativo Disciplinar"),
	AV_REC_SUPERIOR("Av. por Rec. Superior","Avaliação da capacidade laborativa por recomendação superior"),
	AV_READAPTACAO("Av. Readaptação","Avaliação da capacidade laborativa para Fins de Readaptação");
	
	private String description;
	private String shortDescription;
	
	HealthSubject(String shortDescription, String description){
		this.shortDescription = shortDescription;
		this.description = description;
	}
	
	@Override
	public String getDescription() {
		return description;
	}
	
	@Override
	public String getShortDescription() {
		return shortDescription;
	}
	
	@Override
	public int getId() {
	    return ordinal();
	}


	public static List<Subject> getAll() {
		List<Subject> subjectList = new ArrayList<>();
		for(HealthSubject subject : HealthSubject.values()) {
			subjectList.add(subject);
		}
		subjectList.remove(0);
		return subjectList;
	}
	
	public static HealthSubject getSubjectById(int id){
		return HealthSubject.values()[id];
	}
	

}
