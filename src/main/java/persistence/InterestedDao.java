package persistence;

import business.model.Interested;
import business.model.Search;
import persistence.exception.DatabaseException;

/**
 * Estabelece os métodos para ações a serem executadas no banco de dados que guarda informações
 * referente ao interessado do processo.
 * 
 * @author clah
 * @since 05/04/2018
 */

public interface InterestedDao {
	
  /**
   * Salva um Interessado no Banco de Dados.
   * 
   * @param newInterested Interessado a ser salvo no Banco de Dados.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta salvar no banco de
   *         dados.
   */
	/*@ requires newInterested != null;
    @ assignable \nothing;
	@*/
  public void save(Interested newInterested) throws DatabaseException;

  /**
   * Atualiza um Interessado no Banco de Dados.
   * 
   * @param modifiedInterested Interessado a ser modificado no Banco de Dados.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta atualizar no banco de
   *         dados.
   */
/*@ requires modifiedInterested != null;
  @ assignable \nothing;
  @*/
  public void update(Interested modifiedInterested) throws DatabaseException;

  /**
   * Exclui um Interessado do Banco de Dados.
   * 
   * @param interested Interessado a ser deletado.
   * @throws DatabaseException Exceção lançada por inconsistência quando excluir no banco de dados.
   */

/*@ requires interested != null;
  @ assignable \nothing;
  @*/
  public void delete(Interested interested) throws DatabaseException;

  /**
   * Busca um interessado no banco de dados.
   * 
   * @param searchData Dados da busca a ser realizada.
   * @return Interessado encontrado na busca.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta buscar no banco de
   *         dados.
   */
  /*@ requires searchData != null;
  @ assignable \nothing;
  @*/
  public Interested search(Search searchData) throws DatabaseException;


}
