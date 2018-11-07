package juridical.model;

import java.util.ArrayList;
import java.util.List;

import business.model.Subject;

public enum JuridicalJudge implements Subject {
	NULL("INV","- Inválido -"),
	JPFN_JT("Joao Paulo Ferreira Neto","Juiz Titular"),
	MFJ_JD("Maria Fernanda Jordão","Juiz de Direito"),
	JPF_JT("José Pedro Fontes","Juiz Titular"),
	FGM_JD("Fernando Gonçalves Marques","Juiz de Direito"),
	JLO_JD("Júlia Luna Oliveira","Juiz de Direito"),
	CAS_JT("Carla Almeida Silva","Juiz Titular")
	;
	
	private String description;
	private String cargo;
	
	private JuridicalJudge(String description, String cargo) {
		this.description = description;
		this.cargo = cargo;
	}

	@Override
	public String getDescription() {
		return this.description;
	}

	@Override
	public String getShortDescription() {
		return name();
	}
	
	public String getCargo() {
		return cargo;
	}

	@Override
	public int getId() {
	    return ordinal();
	}

	public static List<Subject> getAll() {
		List<Subject> subjectList = new ArrayList<>();
		for(JuridicalJudge subject : JuridicalJudge.values()) {
			subjectList.add(subject);
		}
		subjectList.remove(0);
		return subjectList;
	}
	
	public static JuridicalJudge getSubjectById(int id){
		return JuridicalJudge.values()[id];
	}
}
