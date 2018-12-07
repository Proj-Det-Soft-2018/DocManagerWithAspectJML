package presentation;

import business.service.InterestedService;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;

public abstract class ControllerFactory {

  protected /*@ spec_public nullable @*/ ProcessService processService;
  protected /*@ spec_public nullable @*/ InterestedService interestedService;
  protected /*@ spec_public nullable @*/ ListService listService;
  protected /*@ spec_public nullable @*/ StatisticService statisticService;


  protected ControllerFactory(ProcessService processService, InterestedService interestedService,
      ListService listService, StatisticService statisticService) {
    this.processService = processService;
    this.interestedService = interestedService;
    this.listService = listService;
    this.statisticService = statisticService;
  }

  public PdfViewerCtrl createPdfViewerCtrl() {
    return new PdfViewerCtrl(processService);
  }

  public DeleteDialogCtrl createDeleteDialogCtrl() {
    return new DeleteDialogCtrl(processService);
  }

  public StatisticsScreenCtrl createStatisticsScreenCtrl() {
    return new StatisticsScreenCtrl(statisticService, processService, listService);
  }

  public abstract MainScreenCtrl createMainScreenCtrl();

  public abstract ProcessEditCtrl createProcessEditCtrl();

  public abstract InterestedEditCtrl createInterestedEditCtrl();

  public abstract SearchScreenCtrl createSearchScreenCtrl();
}
