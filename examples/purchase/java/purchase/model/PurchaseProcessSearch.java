package purchase.model;

import business.exception.ValidationException;
import business.model.Search;

public class PurchaseProcessSearch implements Search {

	private String number;
    private String businessName;
    private String cnpj; 
    private int situationId;
    private int organizationId;
    private int subjectId;

    @Override
    public void validate() throws ValidationException {
        boolean invalidNumber = (number == null || number.isEmpty());
        boolean invalidBusinessName = (businessName == null || businessName.isEmpty());
        boolean invalidCnpj = (cnpj == null || cnpj.isEmpty());
        boolean invalidSituation = (situationId == 0);
        boolean invalidOrganization = (organizationId == 0);
        boolean invalidSubject = (subjectId == 0);

        if(invalidNumber && invalidBusinessName && invalidCnpj && invalidSituation && invalidOrganization && invalidSubject) {
            throw new ValidationException("Não foram inseridos valores para busca!");
        }
    }

    public String getNumber() {
        return number;
    }

    public void setNumber(String number) {
        this.number = number;
    }

    public String getBusinessName() {
        return businessName;
    }

    public void setBusinessName(String businessName) {
        this.businessName = businessName;
    }

    public String getCnpj() {
        return cnpj;
    }

    public void setCnpj(String cnpj) {
        this.cnpj = cnpj;
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
