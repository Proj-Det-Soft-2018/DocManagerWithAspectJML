package juridical.persistence;

import persistence.DaoFactory;
import persistence.InterestedDao;
import persistence.ProcessDao;

public class DaoFactoryJDBC implements DaoFactory {
	
	@Override
	public ProcessDao getProcessDao(){
		return new JuridicalProcessDaoJDBC();
	}
	
	@Override
	public InterestedDao getInterestedDao(){
		return new JuridicalInterestedDaoJDBC();
	}
}
