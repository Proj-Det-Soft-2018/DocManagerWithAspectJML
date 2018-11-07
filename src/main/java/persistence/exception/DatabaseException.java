package persistence.exception;

/**
 * Exceção responsável por sinalizar todos os erros relacionados a Banco de Dados e JDBC.
 */
@SuppressWarnings("serial")
public class DatabaseException extends Exception {

  public DatabaseException(String message, Throwable ex) {
    super(message, ex);
  }
}
