package health.presentation;

import business.service.InterestedService;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;
import presentation.ControllerFactory;
import presentation.InterestedEditCtrl;
import presentation.MainScreenCtrl;
import presentation.ProcessEditCtrl;
import presentation.SearchScreenCtrl;

public class HealthControllerFactory extends ControllerFactory {

	public HealthControllerFactory(ProcessService processService, InterestedService interestedService,
			ListService listService, StatisticService statisticService) {
		super(processService, interestedService, listService, statisticService);
	}

	@Override
	public MainScreenCtrl createMainScreenCtrl() {
		return new HealthMainScreenCtrl (super.processService, this);
	}
	
	@Override
	public InterestedEditCtrl createInterestedEditCtrl() {
		return new HealthInterestedEditCtrl (super.interestedService);
	}
	
	@Override
	public ProcessEditCtrl createProcessEditCtrl() {
	    return new HealthProcessEditCtrl(listService, processService, interestedService, this);
	}

    @Override
    public SearchScreenCtrl createSearchScreenCtrl() {
        return new HealthSearchScreenCtrl(processService, listService, this);
    }
}
