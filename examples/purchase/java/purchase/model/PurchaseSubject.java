package purchase.model;

import java.util.ArrayList;
import java.util.List;

import business.model.Subject;

public enum PurchaseSubject implements Subject {
	NULL(null,null),
	MTINFO("Material informacional",null),
	EQINFO("Equipamento de informatica",null),
	MLPHIG("Material de limpeza e produtos de higienização", "Mat. limp. e prod. de hig."),
	MTESCR("Material de escritório", null),
	MEDIC("Medicamentos", null),
	MTHOSP("Material hospitalar", null),
	EQPSS("Equipamento de proteção, segurança e socorro", "Eq. prot., seg. e socorro"),
	ALIMEN("Alimentação", null),
	MOVELR("Movelaria em geral", null);
	
	private String description;
	private String shortDescription;
	
	PurchaseSubject(String description, String shortDescription){
		this.description = description;
		this.shortDescription = shortDescription;
	}

	@Override
	public String getDescription() {
		return description;
	}
	
	@Override
	public String getShortDescription() {
		if (shortDescription == null) {
			return description;
		}
		return shortDescription;
	}
	
	@Override
	public int getId() {
	    return ordinal();
	}

	public static List<Subject> getAll() {
		List<Subject> subjectList = new ArrayList<>();
		for(PurchaseSubject subject : PurchaseSubject.values()) {
			subjectList.add(subject);
		}
		subjectList.remove(0);
		return subjectList;
	}
	
	public static PurchaseSubject getSubjectById(int id){
		return PurchaseSubject.values()[id];
	}
}
