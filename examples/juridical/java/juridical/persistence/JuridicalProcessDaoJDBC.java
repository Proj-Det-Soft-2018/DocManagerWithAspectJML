package juridical.persistence;

import java.sql.Connection;
import java.sql.Date;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Timestamp;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import business.exception.ValidationException;
import business.model.Interested;
import business.model.Process;
import business.model.Search;
import health.persistence.ConnectionFactory;
import juridical.model.JuridicalInterested;
import juridical.model.JuridicalJudge;
import juridical.model.JuridicalOrganization;
import juridical.model.JuridicalProcess;
import juridical.model.JuridicalProcessSearch;
import juridical.model.JuridicalSituation;
import persistence.ProcessDao;
import persistence.exception.DatabaseException;

public class JuridicalProcessDaoJDBC implements ProcessDao {

	@Override
	public void save(Process process) throws DatabaseException, ValidationException {
		JuridicalProcess juridicalProcess = (JuridicalProcess)process;

		String sql = "INSERT INTO inventario"
				+ "(numero,inventariante_id,"
				+ "assunto,situacao,vara,"
				+ "advogado, inventariado, observacao, data_entrada)"
				+ " values (?,?,?,?,?,?,?,?,?)";

		Connection connection = null;
		PreparedStatement statement=null;
		try {
			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement(sql);

			statement.setString(1, juridicalProcess.getNumber());
			statement.setLong(2, juridicalProcess.getInventorian().getId());
			statement.setLong(3, juridicalProcess.getJudge().getId());
			statement.setInt(4, juridicalProcess.getSituation().getId());
			statement.setInt(5, juridicalProcess.getCourt().getId());
			statement.setString(6, juridicalProcess.getLawyerName());
			statement.setString(7, juridicalProcess.getInventoriedName());
			statement.setString(8, juridicalProcess.getObservation());

			//Definindo data de entrada no banco de dados
			LocalDateTime date = LocalDateTime.now();
			juridicalProcess.setRegistrationDate(date);

			Timestamp stamp = Timestamp.valueOf(date);
			Date registrationDate = new Date (stamp.getTime());

			statement.setDate(9,registrationDate);
			statement.executeUpdate();


		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível salvar o processo no Banco de Dados.", e);
		}finally {
			ConnectionFactory.closeConnection(connection, statement);
		}

	}

	@Override
	public void update(Process process) throws DatabaseException {
		JuridicalProcess juridicalProcess = (JuridicalProcess)process;

		String query = "UPDATE inventario SET "
				+ "numero=?, inventariante_id=?, assunto=?,"
				+ "situacao=?, vara=?, advogado=?,"
				+ "inventariado=?, observacao=?,"
				+ " WHERE id=?";

		Connection connection = null;
		PreparedStatement statement=null;

		try {

			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement(query);
			statement.setString(1, juridicalProcess.getNumber());
			statement.setLong(2, juridicalProcess.getInventorian().getId());
			statement.setInt(3, juridicalProcess.getJudge().getId());
			statement.setInt(4, juridicalProcess.getSituation().getId());
			statement.setInt(5, juridicalProcess.getCourt().getId());
			statement.setString(6, juridicalProcess.getLawyerName());
			statement.setString(7, juridicalProcess.getInventoriedName());
			statement.setString(8, juridicalProcess.getObservation());

			//setando id do processo a ser modificado
			statement.setLong(9, juridicalProcess.getId());


			statement.executeUpdate();


		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível atualizar o processo no Banco de Dados.", e);
		}finally {
			ConnectionFactory.closeConnection(connection, statement);
		}

	}

	@Override
	public void delete(Process process) throws DatabaseException {
		Connection connection = null;
		PreparedStatement statement=null;

		try {
			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement("DELETE FROM inventario WHERE id=?");
			statement.setLong(1, process.getId());
			statement.executeUpdate();


		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível deletar o processo do Banco de Dados.", e);
		}finally {
			ConnectionFactory.closeConnection(connection, statement);
		}
	}

	@Override
	public List<Process> getAllProcessesByPriority() throws DatabaseException {
		String sql = " ORDER BY data_entrada ASC, idade DESC" +
				" LIMIT 50";
		return pullProcessList(sql);
	}

	@Override
	public List<Process> searchByNumber(String number) throws DatabaseException {
		String sql = "WHERE numero LIKE '"+number+"'";
		return this.pullProcessList(sql);
	}

	@Override
	public List<Process> searchAll(Search searchData) throws DatabaseException {

		JuridicalProcessSearch search = (JuridicalProcessSearch) searchData;
		StringBuilder sql = new StringBuilder("WHERE ");
		final String AND = " AND ";

		String number = search.getNumber();
		if (number != null && !number.equalsIgnoreCase("")) {
			sql.append("numero LIKE '"+number+"' AND ");
		}

		String name = search.getInventorian();
		if (name != null && !name.equalsIgnoreCase("")) {
			sql.append("nome LIKE '%"+name+"%' AND ");
		}

		String cpf = search.getCpf();
		if (cpf != null && !cpf.equalsIgnoreCase("")) {
			sql.append("cpf= '"+cpf+"' AND ");
		}
		
		String lawyer = search.getLawyer();
		if (lawyer != null && !lawyer.equalsIgnoreCase("")) {
			sql.append("advogado LIKE '"+lawyer+"' AND ");
		}
		
		String inventoried = search.getInventaried();
		if (inventoried != null && !inventoried.equalsIgnoreCase("")) {
			sql.append("inventatiado LIKE '"+cpf+"' AND ");
		}

		int organizationId = search.getCourtId();
		if (organizationId != 0) {
			sql.append("orgao_origem="+organizationId+AND);
		}

		int subjectId = search.getJudgeId();
		if (subjectId != 0) {
			sql.append("assunto="+subjectId+AND);
		}

		int situationId = search.getSituationId();
		if (situationId != 0) {
			sql.append("situacao="+situationId);
		} else {
			sql.delete(sql.lastIndexOf(AND), sql.length());
		}
		return this.pullProcessList(sql.toString());

	}

	private List<Process> pullProcessList(String whereStament) throws DatabaseException {

		Connection connection = null;
		PreparedStatement statement = null;
		ResultSet resultSet = null;
		String query = "SELECT * "
				+ "FROM inventario p "
				+ "INNER JOIN inventariante i "
				+ "ON p.inventariante_id=i.id "
				+ whereStament;

		List<Process> processList = new ArrayList<>();

		try {
			connection = ConnectionFactory.getConnection();

			statement = connection.prepareStatement(query);

			resultSet = statement.executeQuery();

			while(resultSet.next()) {

				//criando objeto Interessado
				Interested interested = new JuridicalInterested(
						resultSet.getLong("inventariante_id"),
						resultSet.getString("nome"),
						resultSet.getInt("idade"),
						resultSet.getString("cpf"),
						resultSet.getString("contato"),
						resultSet.getString("email"));

				//criando o objeto Processo
				JuridicalProcess process = new JuridicalProcess();
				process.setNumber(resultSet.getString("numero"));
				process.setCourt(JuridicalOrganization.getOrganizationById(resultSet.getInt("vara")));
				process.setJudge(JuridicalJudge.getSubjectById(resultSet.getInt("assunto")));
				process.setSituation(JuridicalSituation.getSituationById(resultSet.getInt("situacao")));
				process.setObservation(resultSet.getString("observacao"));
				process.setInventoriedName(resultSet.getString("inventariado"));
				process.setLawyerName(resultSet.getString("advogado"));
				process.setInventorian(interested);


				//Convertendo data entrada de java.sql.Date para LocalDateTime
				Date jdbcRegistrationDate = resultSet.getDate("data_entrada");
				if(jdbcRegistrationDate != null) {
					Timestamp jdbcRegistrationStamp = new Timestamp(jdbcRegistrationDate.getTime());
					LocalDateTime registrationDate = jdbcRegistrationStamp.toLocalDateTime();
					process.setRegistrationDate(registrationDate);
				}
				
				processList.add(process);

			}
		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível buscar o processo no Banco.", e);
		}finally {
			ConnectionFactory.closeConnection(connection, statement, resultSet);
		}

		return processList;
	}

	@Override
	public Map<Integer, ArrayList<Integer>> getQuantityProcessPerMonthYearList() throws DatabaseException {
		String query = "SELECT COUNT(id), EXTRACT(year from data_entrada) as ano, EXTRACT(month from data_entrada) AS mes "
				+ "FROM inventariante "
				+ "GROUP BY ano, mes ORDER BY ano, mes";

		return this.builderMapIntArrayInt(query);
	}

	private Map<Integer, ArrayList<Integer>> builderMapIntArrayInt(String query) throws DatabaseException {
		Connection connection = null;
		PreparedStatement statement = null;
		ResultSet resultSet = null;

		Map<Integer, ArrayList<Integer>> list = new HashMap<>();

		connection = ConnectionFactory.getConnection();

		try {
			statement = connection.prepareStatement(query);
			resultSet = statement.executeQuery();

			while(resultSet.next()) {
				ArrayList<Integer> row = new ArrayList<>();
				if (!list.containsKey(resultSet.getInt("ano")))
				{
					row.add(resultSet.getInt("mes"));
					row.add(resultSet.getInt("count(id)"));
					list.put(resultSet.getInt("ano"), row);
				}else{
					ArrayList<Integer> newRow = list.get(resultSet.getInt("ano"));
					newRow.add(resultSet.getInt("mes"));
					newRow.add(resultSet.getInt("count(id)"));
				}
			}

			return list;

		} catch (SQLException e) {
			throw new DatabaseException("Problema no JDBC", e);
		}
		finally {
			ConnectionFactory.closeConnection(connection, statement, resultSet);
		}
	}

	@Override
	public Map<Integer, Integer> getQuantityProcessPerSituationList() throws DatabaseException {
		String category = "situacao";
		return this.builderMapIntInt(category);
	}

	private Map<Integer, Integer> builderMapIntInt(String categoryColumn) throws DatabaseException{
		Connection connection = null;
		PreparedStatement statement = null;
		ResultSet resultSet = null;

		String query = "SELECT COUNT(id) AS qtde, " + categoryColumn +" FROM inventariante "
				+ "GROUP BY "+ categoryColumn +" ORDER BY "+ categoryColumn;

		Map<Integer, Integer> list = new HashMap<>();

		connection = ConnectionFactory.getConnection();

		try {
			statement = connection.prepareStatement(query);
			resultSet = statement.executeQuery();

			while(resultSet.next()) {
				Integer situation;
				Integer quantity;
				situation = resultSet.getInt(categoryColumn);
				quantity = resultSet.getInt("qtde");

				list.put(situation, quantity);
			}

			return list;

		} catch (SQLException e) {
			throw new DatabaseException("Problema no JDBC", e);
		}finally {
			ConnectionFactory.closeConnection(connection, statement, resultSet);
		}
	}

	@Override
	public Map<Integer, ArrayList<Integer>> getQuantityProcessPerMonthFromLastYearList() throws DatabaseException {
		String query = "SELECT COUNT(id), EXTRACT(year from data_entrada) as ano, EXTRACT(month from data_entrada) AS mes "
				+ "FROM (SELECT * FROM processos WHERE data_entrada BETWEEN CURDATE() - INTERVAL 1 YEAR AND CURDATE() ) AS processosUltimoAno "
				+ "GROUP BY ano, mes ORDER BY ano, mes";
		return this.builderMapIntArrayInt(query);
	}

	@Override
	public Map<Integer, Integer> getQuantityProcessPerOrganizationList() throws DatabaseException {
		String category = "vara";
		return this.builderMapIntInt(category);
	}

	@Override
	public Map<Integer, Integer> getQuantityProcessPerSubjectList() throws DatabaseException {
		String category = "assunto";
		return this.builderMapIntInt(category);
	}

}
