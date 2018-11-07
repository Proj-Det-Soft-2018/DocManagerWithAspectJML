package business.model;

import business.exception.ValidationException;

/**
 * Representação de um Objeto Buscável.
 */
public interface Search {

  /**
   * Validação de um objeto Buscável.
   * 
   * @throws ValidationException Exceção lançada por problemas de validação do buscador.
   */
  void validate() throws ValidationException;
}
