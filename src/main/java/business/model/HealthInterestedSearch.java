package business.model;

import business.exception.ValidationException;

public class HealthInterestedSearch implements Search {
    
    String cpf;

    @Override
    public void validate() throws ValidationException {
        if(cpf == null || cpf.length() != 11) {
            throw new ValidationException("O CPF buscado está incompleto!");
        }
    }

    public String getCpf() {
        return cpf;
    }

    public void setCpf(String cpf) {
        this.cpf = cpf;
    }
}
