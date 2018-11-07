/**
 * 
 */
package juridical.model;

import java.util.ArrayList;
import java.util.List;

import business.model.Organization;

/**
 * @author clah
 *
 */
public enum JuridicalOrganization implements Organization {
	NULL("- Inválido -","Invalido"),
	VSNAT1("1ª Vara de Sucessões da Comarca de Natal","1ª VS Natal"),
	VSNAT2("2ª Vara de Sucessões da Comarca de Natal","2ª VS Natal"),
	VSNAT3("3ª Vara de Sucessões da Comarca de Natal","3ª VS Natal"),
	VSMOS1("1ª Vara de Sucessões da Comarca de Mossoró","1ª VS Mossoró"),
	;
	
	private String description;
	private String initials;
	
	
	private JuridicalOrganization(String description, String initials) {
		this.description = description;
		this.initials = initials;
	}
	
	@Override
	public String getFullName() {
		return this.description;
	}

	@Override
	public String getInitials() {
		return this.initials;
	}

	@Override
	public int getId() {
		return ordinal();
	}
	
	public static List<Organization> getAll() {
		List<Organization> organizationList = new ArrayList<>();
		for(JuridicalOrganization organization : JuridicalOrganization.values()) {
			organizationList.add(organization);
		}
		organizationList.remove(0);
		return organizationList;
	}
	
	public static JuridicalOrganization getOrganizationById(int id){
		return JuridicalOrganization.values()[id];
	}
}
