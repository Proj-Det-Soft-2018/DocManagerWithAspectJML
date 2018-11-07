/**
 * 
 */
package juridical.presentation;

import business.service.InterestedService;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;
import presentation.ControllerFactory;
import presentation.InterestedEditCtrl;
import presentation.MainScreenCtrl;
import presentation.ProcessEditCtrl;
import presentation.SearchScreenCtrl;

/**
 * @author clah
 *
 */
public class JuridicalControllerFactory extends ControllerFactory {

	public JuridicalControllerFactory(ProcessService processService, InterestedService interestedService,
			ListService listService, StatisticService statisticService) {
		super(processService, interestedService, listService, statisticService);
	}

	@Override
	public MainScreenCtrl createMainScreenCtrl() {
		return new JuridicalMainScreenCtrl (super.processService, this);
	}

	@Override
	public ProcessEditCtrl createProcessEditCtrl() {
		return new JuridicalProcessEditCtrl (listService, processService, interestedService, this);
	}

	@Override
	public InterestedEditCtrl createInterestedEditCtrl() {
		return new JuridicalInterestedEditCtrl (super.interestedService);
	}


	@Override
	public SearchScreenCtrl createSearchScreenCtrl() {
		return new JuridicalSearchScreenCtrl (processService, listService, this);
	}

}
