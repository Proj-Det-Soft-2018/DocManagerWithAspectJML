package business.service;

import business.exception.ValidationException;
import business.model.Interested;
import business.model.Search;
import persistence.exception.DatabaseException;

/**
 * Estabelece os métodos para gerenciamento de serviços do interessado do processo.
 * 
 * @author Clarissa - clahzita@gmail.com
 *
 */
public interface InterestedService {

  /**
   * Salva o interessado no banco de dados após validação.
   * 
   * @param interested interessado que deverá ser salvo no banco de dados.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta salvar no banco de
   *         dados.
   */
  public void save(/*@ non_null @*/Interested interested) throws DatabaseException;

  /**
   * Atualiza o interessado no banco de dados após validação.
   * 
   * @param interested interessado que deverá ser atualizado no banco de dados.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta atualizar interessado
   *         no banco de dados.
   */
  public void update(/*@ non_null @*/Interested interested) throws DatabaseException;

  /**
   * Exclui o interessado no banco de dados.
   * 
   * @param interested interessado que deverá ser excluído no banco de dados.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta excluir interessado
   *         no banco de dados.
   */
  public void delete(/*@ non_null @*/Interested interested) throws DatabaseException;

  /**
   * Busca o interessado de acordo com os parametros estabelecidos no searchData.
   * 
   * @param searchData Objeto que guarda os parametros de busca do interessado.
   * @return Interessado que atende os parametros de busca ou null se nenhum foi encontrado.
   * @throws ValidationException Exceção lançada por problemas de validação do objeto buscável.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta procurar no banco de
   *         dados.
   */
  public /*@ nullable @*/Interested search(/*@ non_null @*/ Search searchData) throws ValidationException, DatabaseException;

  /**
   * Anexa um observador na classe para que seja notificado quando ocorre mudanças na lista de
   * interessados.
   * 
   * @param observer observador que será anexado.
   */
  public void attach(/*@ non_null @*/Observer observer);

  /**
   * Desanexa um observador na classe para que não seja mais notificado quando ocorrer mudanças na
   * lista de interessados.
   * 
   * @param observer observador que será desanexado.
   */
  public void dettach(/*@ non_null @*/Observer observer);
}
