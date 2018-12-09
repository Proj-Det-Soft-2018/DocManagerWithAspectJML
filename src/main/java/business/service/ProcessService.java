package business.service;

import business.exception.ValidationException;
import business.model.Process;
import business.model.Search;
import java.util.List;
import persistence.exception.DatabaseException;

/**
 * Estabelece os métodos para gerenciamento de serviços do processo.
 *
 */
public interface ProcessService {

  /**
   * Retorna a lista de processos para ser exibida na tabela da tela principal.
   * 
   * @return Lista com todos os processos organizados de acordo com o que determina a prioridade
   *         atual.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta pegar a lista no
   *         banco de dados.
   */
  public List<Process> pullList() throws DatabaseException;

  /**
   * Salva o processo no banco de dados após validação de regras de negócio.
   * 
   * @param process Processo que deverá ser salvo no banco de dados.
   * @throws ValidationException Exceção lançada por problemas de validação do processo.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta salvar no banco de
   *         dados.
   */
  public void save(/*@ non_null @*/Process process) throws ValidationException, DatabaseException;

  /**
   * Atualiza os dados do processo no banco de dados após validação de regars de negócio.
   * 
   * @param process Processo que deverá ser atualizado no banco de dados.
   * @throws ValidationException Exceção lançada por problemas de validação do processo.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta atualizar processo no
   *         banco de dados.
   */
  //@ requires process.getId()!=null;
  public void update(/*@ non_null @*/Process process) throws ValidationException, DatabaseException;

  /**
   * Exclui o processo no banco de dados.
   * 
   * @param process Processo que deverá ser excluído no banco de dados.
   * @param admUser Usuário administrador que tem permissão para excluir processos do sistema.
   * @param password Senha do administrador.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta excluir interessado
   *         no banco de dados.
   */
  //@ requires process.getId()!=null && !admUser.isEmpty() && !password.isEmpty();
  public void delete(/*@ non_null @*/Process process, /*@ non_null @*/String admUser, /*@ non_null @*/String password) throws DatabaseException;

  /**
   * Busca o processo de acordo com os parametros estabelecidos no searchData.
   * 
   * @param searchData Objeto que guarda os parametros de busca do processo.
   * @return Processo(s) que atende(m) os parametros de busca ou null se nenhum foi encontrado.
   * @throws ValidationException Exceção lançada por problemas de validação do objeto buscável.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta procurar no banco de
   *         dados.
   */
  public List<Process> searchAll(/*@ non_null @*/Search searchData) throws ValidationException, DatabaseException;

  /**
   * Obtém um binário com o documento Pdf gerado a partir do processo fornecido por parâmetro.
   * 
   * @param process Processo para geração do Pdf.
   * 
   * @return Binário do Pdf.
   */
  public byte[] getPdf(/*@ non_null @*/Process process);

  /**
   * Anexa um observador na classe para que seja notificado quando ocorre mudanças na lista de
   * processos.
   * 
   * @param observer observador que será anexado.
   */
  public void attach(/*@ non_null @*/Observer observer);

  /**
   * Desanexa um observador da classe para que não seja mais notificado quando ocorrer mudanças na
   * lista de processos.
   * 
   * @param observer observador que será desanexado.
   */
  public void dettach(/*@ non_null @*/Observer observer);
}
