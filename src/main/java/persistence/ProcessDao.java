package persistence;

import business.exception.ValidationException;
import business.model.Process;
import business.model.Search;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import persistence.exception.DatabaseException;

/**
 * Estabelece os métodos para ações a serem executadas no banco de dados que guarda informações
 * referente ao processo.
 */
public interface ProcessDao {

  /**
   * Salva um Processo no Banco de Dados.
   * 
   * @param newProcess Processo a ser inserido no Banco de Dados
   * @throws ValidationException Exceção lançada por problemas de validação do processo.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta salvar no banco de
   *         dados.
   */
  public void save(Process newProcess) throws DatabaseException, ValidationException;

  /**
   * Atualiza um Processo no Banco de Dados.
   * 
   * @param modifiedProcess Projeto a ser modificado.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta atualizar processo no
   *         banco de dados.
   */
  public void update(Process modifiedProcess) throws DatabaseException;

  /**
   * Deleta um Processo do Banco de Dados.
   * 
   * @param process Processo a ser deletado.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta excluir o processo do
   *         banco de dados.
   */
  public void delete(Process process) throws DatabaseException;

  /**
   * Montar uma lista de processos de acordo com a prioridade definida.
   * 
   * @return Uma lista de processos ordenadas por uma prioridade definida pelo usuário.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta pegar a lista de
   *         processos no banco de dados.
   */
  public List<Process> getAllProcessesByPriority() throws DatabaseException;

  /**
   * Busca um processo através do Número.
   * 
   * @param number Número do processo.
   * @return Lista de Processos com o número passado.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta buscar processo pelo
   *         número no banco de dados.
   */
  public List<Process> searchByNumber(String number) throws DatabaseException;

  /**
   * Busca os processos de acordo com os parametros passados.
   * 
   * @param searchData Objeto de busca com os parametros a serem analisados.
   * @return Lista de processos que satisfizeram a busca.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta buscar processo no
   *         banco de dados.
   */
  public List<Process> searchAll(Search searchData) throws DatabaseException;

  /**
   * Quantidade de Processos em cada mês do ano.
   * 
   * @return Map contendo o ano, o mês e a contagem.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta pegar a lista de
   *         processos no banco de dados.
   */
  public Map<Integer, ArrayList<Integer>> getQuantityProcessPerMonthYearList()
      throws DatabaseException;

  /**
   * Quantidade de Processos por Situação.
   * 
   * @return Map com as situações e a quantidade de processos.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta pegar a lista de
   *         processos no banco de dados.
   */
  public Map<Integer, Integer> getQuantityProcessPerSituationList() throws DatabaseException;

  /**
   * Quantidade de Processos mês a mês no último ano.
   * 
   * @return Map contendo o ano, o mês e a quantidade de processos.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta pegar a lista de
   *         processos no banco de dados.
   */
  public Map<Integer, ArrayList<Integer>> getQuantityProcessPerMonthFromLastYearList()
      throws DatabaseException;

  /**
   * Quantidade de Processos de acordo com as Organização.
   * 
   * @return Map com as Organizações e a quantidade de processos naquela organização.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta pegar a lista de
   *         processos no banco de dados.
   */
  public Map<Integer, Integer> getQuantityProcessPerOrganizationList() throws DatabaseException;

  /**
   * Quantidade de Processos de acordo com o Assunto.
   * 
   * @return Map contendo os Assuntos e os processos que contém o assunto.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta pegar a lista de
   *         processos no banco de dados.
   */
  public Map<Integer, Integer> getQuantityProcessPerSubjectList() throws DatabaseException;

}
