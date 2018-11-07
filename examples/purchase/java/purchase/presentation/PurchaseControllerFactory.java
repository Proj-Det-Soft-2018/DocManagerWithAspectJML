package purchase.presentation;

import business.service.InterestedService;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;
import presentation.ControllerFactory;
import presentation.InterestedEditCtrl;
import presentation.MainScreenCtrl;
import presentation.ProcessEditCtrl;
import presentation.SearchScreenCtrl;

public class PurchaseControllerFactory extends ControllerFactory {
	
	public PurchaseControllerFactory(ProcessService processService, InterestedService interestedService,
			ListService listService, StatisticService statisticService) {
		super(processService, interestedService, listService, statisticService);
	}

	@Override
	public MainScreenCtrl createMainScreenCtrl() {
		return new PurchaseMainScreenCtrl(super.processService, this);
	}

	@Override
	public ProcessEditCtrl createProcessEditCtrl() {
		return new PurchaseProcessEditCtrl(super.listService, super.processService, super.interestedService, this);
	}

	@Override
	public InterestedEditCtrl createInterestedEditCtrl() {
		return new PurchaseInterestedEditCtrl(super.interestedService);
	}

	@Override
	public SearchScreenCtrl createSearchScreenCtrl() {
		return new PurchaseSearchScreenCtrl(super.processService, super.listService, this);
	}

}
