package persistence;

/**
 * Estabelece métodos que para implementação de uma fábrica de Daos.
 */
public interface DaoFactory {

  /**
   * Retorna um objeto responsavel por acessar o banco de dados do processo.
   * 
   * @return Objeto de acesso ao banco de dados do processo.
   */
  ProcessDao getProcessDao();

  /**
   * Retorna um objeto responsavel por acessar o banco de dados do interessado do processo.
   * 
   * @return Objeto de acesso ao banco de dados do interessado do processo.
   */
  InterestedDao getInterestedDao();
}
