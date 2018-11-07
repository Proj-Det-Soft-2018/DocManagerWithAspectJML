package business.service;

import java.util.ArrayList;
import java.util.Map;
import persistence.exception.DatabaseException;

/**
 * Estabelece os métodos para gerenciamento de serviços de gráficos estatísticos dos processos.
 * guardados no banco de dados.
 * 
 * @author clarissa - clahzita@gmail.com
 * @since 04.20.2018
 */
public interface StatisticService {

  /**
   * Retorna um map que guarda a quantidade de processos registrados em cada mês do ano.
   * 
   * @return Map em que a chave é o mês e o valor é uma lista de com as quantidades em cada mês.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta buscar os processos
   *         no banco de dados.
   */
  public Map<Integer, ArrayList<Integer>> quantityProcessPerMonthYear() throws DatabaseException;

  /**
   * Retorna um map que guarda a quantidade de processos registrados no último ano.
   * 
   * @return Map em que a chave é o mês dos ultimo ano e o valor é uma lista de com as quantidades
   *         de processos em cada mês.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta buscar os processos
   *         no banco de dados.
   */
  public Map<Integer, ArrayList<Integer>> quantityProcessFromLastYear() throws DatabaseException;

  /**
   * Retorna um map que guarda a quantidade de processos de acordo com a situação.
   * 
   * @return Map em que a chave é o identificador da situação e o valor é quantidade de processos
   *         registrados naquela situação.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta buscar os processos
   *         no banco de dados.
   */
  public Map<Integer, Integer> quantityProcessPerSituation() throws DatabaseException;

  /**
   * Retorna um map que guarda a quantidade de processos de acordo com a organização que pertence.
   * 
   * @return Map em que a chave é o identificador da organização e o valor é quantidade de processos
   *         registrados naquela organização.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta buscar os processos
   *         no banco de dados.
   */
  public Map<Integer, Integer> quantityProcessPerOrganization() throws DatabaseException;

  /**
   * Retorna um map que guarda a quantidade de processos de acordo com seu assunto.
   * 
   * @return Map em que a chave é o identificador do assunto e o valor é quantidade de processos
   *         registrados com aquele assunto.
   * @throws DatabaseException Exceção lançada por inconsistência quando tenta buscar os processos
   *         no banco de dados.
   */
  public Map<Integer, Integer> quantityProcessPerSubject() throws DatabaseException;

}
