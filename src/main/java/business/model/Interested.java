package business.model;

import business.exception.ValidationException;

/**
 * Representação de um Interessado em um Processo.
 */
public interface Interested {

  Long getId();

  void setId(Long id);

  /**
   * Método que realiza a validação do Interessado.
   * 
   * @throws ValidationException Exceção lançada por problemas de validação do interessado.
   */
  public void validate() throws ValidationException;

}
