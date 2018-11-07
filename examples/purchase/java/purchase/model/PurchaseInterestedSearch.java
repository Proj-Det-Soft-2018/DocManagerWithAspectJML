package purchase.model;

import business.exception.ValidationException;
import business.model.Search;

public class PurchaseInterestedSearch implements Search {

	String cnpj;

    @Override
    public void validate() throws ValidationException {
        if(cnpj == null || cnpj.length() != 14) {
            throw new ValidationException("O CNPJ buscado está incompleto!");
        }
    }

    public String getCnpj() {
        return cnpj;
    }

    public void setCnpj(String cnpj) {
        this.cnpj = cnpj;
    }
}
