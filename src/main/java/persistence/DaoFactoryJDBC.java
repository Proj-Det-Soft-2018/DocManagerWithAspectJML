package persistence;

import persistence.DaoFactory;
import persistence.InterestedDao;
import persistence.ProcessDao;

public class DaoFactoryJDBC implements DaoFactory {
	
	@Override
	public ProcessDao getProcessDao(){
		return new HealthProcessDaoJDBC();
	}
	
	@Override
	public InterestedDao getInterestedDao(){
		return new HealthInterestedDaoJDBC();
	}

}
