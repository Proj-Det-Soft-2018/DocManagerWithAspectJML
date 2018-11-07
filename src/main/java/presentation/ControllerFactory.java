package presentation;

import business.service.InterestedService;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;

/**
 * Classe abstrata que representa a fábrica de controladores JavaFX para o framework. Como é um dos
 * pontos flexíveis do framework, o desenvolvedor deve implementar seus métodos abstratos para obter
 * os controladores da telas Principal, de Edição de Processos, de edição de Interessados e de
 * Busca, sendo já oferecidos os controladores das telas de visualização de PDF, confirmação de
 * apagamento de processo e de estatísticas.
 * 
 * @author hugo
 */
public abstract class ControllerFactory {

  /**
   * Serviço para processamento de objetos que implementem a interface {@code Process}.
   */
  protected ProcessService processService;
  /**
   * Serviço para processamento de objetos que implementem a interface {@code Interested}.
   */
  protected InterestedService interestedService;
  /**
   * Serviço para obtenção e processamento das listas que abastencem as telas das aplicações geradas
   * com o framework
   */
  protected ListService listService;
  /**
   * Serviço para obtenção de estatísticas de utilização do sistema.
   */
  protected StatisticService statisticService;


  /**
   * Construtor da fábrica, deve ser chamado no construtor as classes que extenderão esta.
   * 
   * @param processService Serviço de processamento de processos.
   * @param interestedService Serviço de processamento de interessados.
   * @param listService Serviço para obtenção de listas de situação e demais dados.
   * @param statisticService Serviço para processamento das estatísticas do sistema.
   */
  protected ControllerFactory(ProcessService processService, InterestedService interestedService,
      ListService listService, StatisticService statisticService) {
    this.processService = processService;
    this.interestedService = interestedService;
    this.listService = listService;
    this.statisticService = statisticService;
  }

  /**
   * Cria um novo controlador da tela de visualização de PDF, que é abastecido pelo serviço de pro-
   * cessamento de processos injetado na fábrica.
   * 
   * @return Novo controlador para tela de visualização de PDF.
   */
  public PdfViewerCtrl createPdfViewerCtrl() {
    return new PdfViewerCtrl(processService);
  }

  /**
   * Cria um novo controlador da tela de confirmação de deleção, que é abastecido pelo serviço de
   * processamento de processos injetado na fábrica.
   * 
   * @return Novo controlador para tela confirmação de deleção.
   */
  public DeleteDialogCtrl createDeleteDialogCtrl() {
    return new DeleteDialogCtrl(processService);
  }

  /**
   * Cria um novo controlador da tela de visualização de estatísticas, que é abastecido pelo serviço
   * de estatística e pelo de listas injetados na fábrica.
   * 
   * @return Novo controlador para tela de estatísticas.
   */
  public StatisticsScreenCtrl createStatisticsScreenCtrl() {
    return new StatisticsScreenCtrl(statisticService, processService, listService);
  }

  /**
   * Método deve ser implementado pelas classes que extendem {@code ControllerFactory} a fim a
   * obtenção de um controlador de extende {@code MainScreenCtrl} para o processamento da tela prin-
   * cipal.
   * 
   * @return Controlador para a tela principal.
   */
  public abstract MainScreenCtrl createMainScreenCtrl();

  /**
   * Método deve ser implementado pelas classes que extendem {@code ControllerFactory} a fim a
   * obtenção de um controlador de extende {@code ProcessEditCtrl} para o processamento da tela de
   * edição dos objetos que extendem {@code Process}.
   * 
   * @return Controlador para a tela de edição de processos.
   */
  public abstract ProcessEditCtrl createProcessEditCtrl();

  /**
   * Método deve ser implementado pelas classes que extendem {@code ControllerFactory} a fim a
   * obtenção de um controlador de extende {@code InterestedEditCtrl} para o processamento da tela
   * de edição dos objetos que extendem {@code Interested}.
   * 
   * @return Controlador para a tela de edição de interessados.
   */
  public abstract InterestedEditCtrl createInterestedEditCtrl();

  /**
   * Método deve ser implementado pelas classes que extendem {@code ControllerFactory} a fim a
   * obtenção de um controlador de extende {@code SearchScreenCtrl} para o processamento da tela de
   * busca.
   * 
   * @return Controlador para a tela de busca.
   */
  public abstract SearchScreenCtrl createSearchScreenCtrl();
}
