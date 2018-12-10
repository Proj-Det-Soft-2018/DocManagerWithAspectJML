import java.util.ArrayList;
import java.util.List;

import business.exception.ValidationException;
import business.model.HealthInterested;
import business.model.HealthInterestedSearch;
import business.model.HealthOrganization;
import business.model.HealthProcess;
import business.model.HealthProcessSearch;
import business.model.HealthSituation;
import business.model.HealthSubject;
import business.model.Organization;
import business.model.Search;
import business.model.Process;
import business.service.ConcreteListService;
import business.service.ConcreteProcessService;
import business.service.ConcreteStatisticService;
import business.service.InterestedService;
import business.service.InterestedServiceImpl;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;
import persistence.DaoFactory;
import persistence.DaoFactoryJDBC;
import persistence.exception.DatabaseException;

public class MainJMLTeste {

	public static void main(String[] args) {
		DaoFactory daoFactory = new DaoFactoryJDBC();
		ProcessService processService = new ConcreteProcessService(daoFactory);
		InterestedService interestedService = new InterestedServiceImpl(daoFactory);
		StatisticService statisticService = new ConcreteStatisticService(daoFactory);

		ListService listService = new ConcreteListService(HealthOrganization.getAll(), HealthSubject.getAll(),
				HealthSituation.getAll());

		// SALVAR UM INTERESSADO
		String cpf = "12345678901";
		// criando um searchData para fazer busca no banco
		Search searchDataInterested = new HealthInterestedSearch();
		((HealthInterestedSearch) searchDataInterested).setCpf(cpf);

		HealthInterested interestedCompleto = new HealthInterested("Maria Almeida", cpf, "3206-775");
		HealthInterested interestedSalvo = null;
		try {
			// salvando no banco
			interestedService.save(interestedCompleto);
			System.out.println("Interssado salvo no banco! Cpf " + interestedCompleto.getCpf());

			// fazendo busca
			interestedSalvo = (HealthInterested) interestedService.search(searchDataInterested);
			// imprimindo resultado da busca
			if (interestedSalvo != null) {
				System.out.println("Busca após salvar interessado! Cpf: " + interestedSalvo.getCpf());

			}
		} catch (DatabaseException e) {
			System.err.println(e.getMessage());
		} catch (ValidationException e) {
			System.err.println(e.getMessage());
		}

		// ALTERAR UM INTERESSADO
		if (interestedSalvo != null) {
			// alterando o nome
			interestedSalvo.setName("Maria Almeida Martins");
			System.out.println("alterando o nome para :" + interestedSalvo.getName());
			try {
				// fazendo atualização
				interestedService.update(interestedSalvo);
				// fazendo busca
				interestedSalvo = (HealthInterested) interestedService.search(searchDataInterested);
				// imprimindo resultado da busca
				if (interestedSalvo != null) {
					System.out.println("Busca após alterar interessado! Cpf: " + interestedSalvo.getCpf());

				}

			} catch (DatabaseException e) {
				System.err.println(e.getMessage());
			} catch (ValidationException e) {
				System.err.println(e.getMessage());
			}
		} else {
			System.err.println("interessado não foi bem sucedido na busca anterior.");
		}

		// EXCLUIR UM INTERESSADO
		if (interestedSalvo != null) {
			try {
				// fazendo atualização
				interestedService.delete(interestedSalvo);

				System.out.println("Exclusao efetuada!");

			} catch (DatabaseException e) {
				System.err.println(e.getMessage());
			}
		} else {
			System.err.println("interessado não foi bem sucedido na busca anterior.");
		}

		// SALVAR PROCESSO
		// colocando cpf de algum interessado que tem no banco
		String cpfInteressadoBanco = "06570588458";
		((HealthInterestedSearch) searchDataInterested).setCpf(cpfInteressadoBanco);

		// preparando buscador do processo
		String numero = "00072018";

		HealthProcessSearch searchDataProcess = new HealthProcessSearch();
		searchDataProcess.setCpf(cpfInteressadoBanco);

		List<Process> processoSalvo = new ArrayList<>();

		try {
			interestedSalvo = (HealthInterested) interestedService.search(searchDataInterested);
			// criando objeto processo sem ID
			Process processo = new HealthProcess(true, numero, interestedSalvo, HealthOrganization.AGU,
					HealthSubject.APO, HealthSituation.CONVOCAR, "obs");

			// salvando processo no banco
			processService.save(processo);
			System.out.println("salvo processo");

			// buscando o processo no banco
//			processoSalvo = ((ConcreteProcessService) processService).searchAll(searchDataProcess);
//			System.out.println();
//			for (Process process : processoSalvo) {
//				System.out.println(((HealthProcess) process).getId());
//			}

		} catch (ValidationException e) {
			System.err.println(e.getMessage());
		} catch (DatabaseException e) {
			System.err.println(e.getMessage());
		}
	}
}
