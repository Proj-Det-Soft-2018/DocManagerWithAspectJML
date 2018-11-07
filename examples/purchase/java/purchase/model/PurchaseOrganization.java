package purchase.model;

import java.util.ArrayList;
import java.util.List;

import business.model.Organization;

public enum PurchaseOrganization implements Organization {
	NULL(null),
	IMD("Instituto Metrópole Digital"),
	RU("Restaurante Universitário"),
	DIMAP("Departamento de Informática e Matemática Aplicada"),
	DMAT("Departamento de Matemática"),
	DCA("Departamento de Engenharia de Computação e Automação"),
	DEST("Departamento de Estatística"),
	ECT("Escola de Ciências & Tecnologia"),
	DAS("Diretoria de Atenção à Saúde do Servidor"),
	HUOL("Hospital Universitário Onofre Lopes"),
	MEJC("Maternidade Escola Januário Cicco"),
	EAJ("Escola Agrícula de Jundiaí"),
	DART("Departamento de Artes"),
	ICe("Instituto do Cérebro"),
	EMURFN("Escola de Música"),
	DOL("Departamento de Oceanografia e Limnologia"),
	DSC("Departamento de Saúde Coletiva"),
	DBQ("Departamento de Bioquímica"),
	DMP("Departamento de Microbiologia e Parasitologia");
	
private String fullName;
	
	PurchaseOrganization(String fullName) {
		this.fullName = fullName;
	}
	
	@Override
	public String getFullName() {
		return fullName;
	}
	
	@Override
	public String getInitials(){
	    return name();
	}
	
	@Override
	public int getId() {
	    return ordinal();
	}

	public static List<Organization> getAll() {
		List<Organization> organizationList = new ArrayList<>();
		for(PurchaseOrganization organization : PurchaseOrganization.values()) {
			organizationList.add(organization);
		}
		organizationList.remove(0);
		return organizationList;
	}
	
	public static PurchaseOrganization getOrganizationById(int id){
		return PurchaseOrganization.values()[id];
	}
}
