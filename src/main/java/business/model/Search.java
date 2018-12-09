package business.model;

import business.exception.ValidationException;

/**
 * Representação de um Objeto Buscável.
 */
public interface Search {
	//@ public model instance String cpfInterested;
  /**
   * Validação de um objeto Buscável.
   * 
   * @throws ValidationException Exceção lançada por problemas de validação do buscador.
   */
	//@ requires this != null;
	//@ ensures !(cpfInterested == null || !(cpfInterested.isEmpty()));
	/*@ pure @*/ void  validate() throws ValidationException;
}
