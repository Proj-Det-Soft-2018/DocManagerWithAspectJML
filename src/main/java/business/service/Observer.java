package business.service;

/**
 * Classe responsável por atualizar o observador quando ocorrer alterações no objeto observável.
 *
 */
public interface Observer {

  /* Atualiza o estado dos observadores. */
  public void update();
}
