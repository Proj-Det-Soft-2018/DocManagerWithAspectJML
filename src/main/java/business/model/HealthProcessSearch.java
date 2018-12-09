package business.model;

import business.exception.ValidationException;
import business.model.Search;

public class HealthProcessSearch implements Search {
    
    private /*@ spec_public nullable @*/ String number;
    private /*@ spec_public nullable @*/ String name;
    private /*@ spec_public nullable @*/ String cpf;
    private /*@ spec_public nullable @*/int situationId;
    private /*@ spec_public nullable @*/int organizationId;
    private /*@ spec_public nullable @*/int subjectId;

    
    /*@ also
    @  public normal_behavior
    @ 		ensures  !(cpf == null || cpf.isEmpty()) ||
    @				 !(number == null || number.isEmpty()) || 
    @ 				 !(name == null || name.isEmpty()) ||
    @ 		         (situationId != 0) || (organizationId != 0) || (subjectId != 0);
    @ also
    @   public exceptional_behavior
    @ 		requires (number == null || number.isEmpty()) && 
    @ 				 (name == null || name.isEmpty()) &&
    @ 		         (cpf == null || cpf.isEmpty()) &&
    @ 		         (situationId == 0) && (organizationId == 0) && (subjectId == 0);
    @		signals_only ValidationException;	 
	 @*/
    @Override
    public void validate() throws ValidationException {
        boolean invalidNumber = (number == null || number.isEmpty());
        boolean invalidName = (name == null || name.isEmpty());
        boolean invalidCpf = (cpf == null || cpf.isEmpty());
        boolean invalidSituation = (situationId == 0);
        boolean invalidOrganization = (organizationId == 0);
        boolean invalidSubject = (subjectId == 0);

        if(invalidNumber && invalidName && invalidCpf && invalidSituation && invalidOrganization && invalidSubject) {
            throw new ValidationException("Não foram inseridos valores para busca!");
        }
    }

    public String getNumber() {
        return number;
    }

    public void setNumber(String number) {
        this.number = number;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getCpf() {
        return cpf;
    }

    public void setCpf(String cpf) {
        this.cpf = cpf;
    }

    public int getSituationId() {
        return situationId;
    }

    public void setSituationId(int situationId) {
        this.situationId = situationId;
    }

    public int getOrganizationId() {
        return organizationId;
    }

    public void setOrganizationId(int organizationId) {
        this.organizationId = organizationId;
    }

    public int getSubjectId() {
        return subjectId;
    }

    public void setSubjectId(int subjectId) {
        this.subjectId = subjectId;
    }
}
