package purchase.persistence;

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
import business.model.Process;
import business.model.Search;
import health.persistence.ConnectionFactory;
import persistence.ProcessDao;
import persistence.exception.DatabaseException;
import purchase.model.PurchaseInterested;
import purchase.model.PurchaseProcess;
import purchase.model.PurchaseProcessSearch;
import purchase.model.PurchaseSituation;

public class PurchaseProcessDaoJDBC implements ProcessDao {

	@Override
	public void save(Process process) throws DatabaseException, ValidationException {
		PurchaseProcess purchaseProcess = (PurchaseProcess)process;
		checkDuplicate(purchaseProcess.getNumber());

		String sql = "INSERT INTO processos_compra"
				+ "(numero, descricao, interessado_id,"
				+ "tipo_material,situacao,unidade_origem,"
				+ "observacao,data_entrada)"
				+ " VALUES (?,?,?,?,?,?,?,?)";

		Connection connection = null;
		PreparedStatement statement=null;
		try {
			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement(sql);

			statement.setString(1, purchaseProcess.getNumber());
			statement.setString(2, purchaseProcess.getDescription());
			statement.setLong(3, purchaseProcess.getInterested().getId());
			statement.setInt(4, purchaseProcess.getSubject().getId());
			statement.setInt(5, purchaseProcess.getSituation().getId());
			statement.setInt(6, purchaseProcess.getOriginEntity().getId());
			statement.setString(7, purchaseProcess.getObservation());

			//Definindo data de entrada no banco de dados
			LocalDateTime date = LocalDateTime.now();
			purchaseProcess.setRegistrationDate(date);

			Timestamp stamp = Timestamp.valueOf(date);
			Date registrationDate = new Date (stamp.getTime());

			statement.setDate(8,registrationDate);
			statement.executeUpdate();


		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível salvar o processo no Banco de Dados.", e);
		}finally {
			ConnectionFactory.closeConnection(connection, statement);
		}
	}

	private void checkDuplicate(String numero) throws ValidationException, DatabaseException {
		List<Process> duplicados = this.searchByNumber(numero);
		if(duplicados != null && !duplicados.isEmpty()) {
			throw new ValidationException("Existe outro processo cadastrado com situação não concluída");			
		}		
	}

	@Override
	public void update(Process process) throws DatabaseException {
		PurchaseProcess purchaseProcess = (PurchaseProcess)process;

		String query = "UPDATE processos_compra SET "
				+ "numero=?, descricao=?, interessado_id=?, tipo_material=?,"
				+ "situacao=?, unidade_origem=?, observacao=?"
				+ " WHERE id=?";

		Connection connection = null;
		PreparedStatement statement=null;

		try {

			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement(query);
			statement.setString(1, purchaseProcess.getNumber());
			statement.setString(2, purchaseProcess.getDescription());
			statement.setLong(3, purchaseProcess.getInterested().getId());
			statement.setInt(4, purchaseProcess.getSubject().getId());
			statement.setInt(5, purchaseProcess.getSituation().getId());
			statement.setInt(6, purchaseProcess.getOriginEntity().getId());
			statement.setString(7, purchaseProcess.getObservation());

			//setando id do processo a ser modificado
			statement.setLong(8, purchaseProcess.getId());

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
			statement = connection.prepareStatement("DELETE FROM processos_compra WHERE id=?");
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
		int paid = PurchaseSituation.PAGOLIQUD.getId();
		int cancel = PurchaseSituation.CANCELADO.getId();
		String sql = "WHERE situacao NOT IN ("+paid+", "+cancel+")" +
				" ORDER BY data_entrada DESC" +
				" LIMIT 50";
		List<Process> intermediaryList = pullProcessList(sql);
		if (intermediaryList.size() < 50) {
			sql = "WHERE situacao IN ("+paid+", "+cancel+")"+
					" ORDER BY data_entrada DESC"+
					" LIMIT "+(50 - intermediaryList.size());
			intermediaryList.addAll(pullProcessList(sql));
		}
		return intermediaryList;
	}

	private List<Process> pullProcessList(String whereStament) throws DatabaseException {

		Connection connection = null;
		PreparedStatement statement = null;
		ResultSet resultSet = null;
		String query = "SELECT * "
				+ "FROM processos_compra p "
				+ "INNER JOIN interessados_compra i "
				+ "ON p.interessado_id=i.id "
				+ whereStament;

		List<Process> processList = new ArrayList<>();

		try {
			connection = ConnectionFactory.getConnection();

			statement = connection.prepareStatement(query);

			resultSet = statement.executeQuery();

			while(resultSet.next()) {

				//criando objeto Interessado
				PurchaseInterested interested = new PurchaseInterested();
				interested.setId(resultSet.getLong("interessado_id"));
				interested.setCnpj(resultSet.getString("cnpj"));
				interested.setBusinessName(resultSet.getString("razao"));
				interested.setLiableName(resultSet.getString("nome_resp"));
				interested.setLiableCpf(resultSet.getString("cpf_resp"));
				interested.setContact(resultSet.getString("contato"));


				//criando o objeto Processo
				PurchaseProcess process = new PurchaseProcess();
				process.setId(resultSet.getLong("id"));
				process.setNumber(resultSet.getString("numero"));
				process.setDescription(resultSet.getString("descricao"));
				process.setObservation(resultSet.getString("observacao"));
				process.setInterested(interested);

				process.setSubjectById(resultSet.getInt("tipo_material"));
				process.setOriginEntityById(resultSet.getInt("unidade_origem"));
				process.setSituationById(resultSet.getInt("situacao"));


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
	public List<Process> searchByNumber(String number) throws DatabaseException {
		String sql = "WHERE numero LIKE '"+number+"'";
		return this.pullProcessList(sql);
	}

	@Override
	public List<Process> searchAll(Search searchData) throws DatabaseException {
		PurchaseProcessSearch search = (PurchaseProcessSearch) searchData;
		StringBuilder sql = new StringBuilder("WHERE ");
		final String AND = " AND ";

		String number = search.getNumber();
		if (number != null && !number.equalsIgnoreCase("")) {
			sql.append("numero LIKE '"+number+"' AND ");
		}

		String businessName = search.getBusinessName();
		if (businessName != null && !businessName.equalsIgnoreCase("")) {
			sql.append("razao LIKE '%"+businessName+"%' AND ");
		}

		String cnpj = search.getCnpj();
		if (cnpj != null && !cnpj.equalsIgnoreCase("")) {
			sql.append("cnpj= '"+cnpj+"' AND ");
		}

		int organizationId = search.getOrganizationId();
		if (organizationId != 0) {
			sql.append("unidade_origem="+organizationId+AND);
		}

		int subjectId = search.getSubjectId();
		if (subjectId != 0) {
			sql.append("tipo_material="+subjectId + AND);
		}

		int situationId = search.getSituationId();
		if (situationId != 0) {
			sql.append("situacao="+situationId);
		} else {
			sql.delete(sql.lastIndexOf(AND), sql.length());
		}

		return this.pullProcessList(sql.toString());
	}

	@Override
	public Map<Integer, ArrayList<Integer>> getQuantityProcessPerMonthYearList() throws DatabaseException {
		String query = "SELECT COUNT(id), EXTRACT(year from data_entrada) as ano, EXTRACT(month from data_entrada) AS mes "
				+ "FROM processos_compra "
				+ "GROUP BY ano, mes ORDER BY ano, mes";

		return builderMapIntArrayInt(query);
	}

	@Override
	public Map<Integer, ArrayList<Integer>> getQuantityProcessPerMonthFromLastYearList() throws DatabaseException {
		String query = "SELECT COUNT(id), EXTRACT(year from data_entrada) as ano, EXTRACT(month from data_entrada) AS mes "
				+ "FROM (SELECT * FROM processos_compra WHERE data_entrada BETWEEN CURDATE() - INTERVAL 1 YEAR AND CURDATE() ) AS processosUltimoAno "
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
	
	@Override
	public Map<Integer, Integer> getQuantityProcessPerOrganizationList() throws DatabaseException {
		String category = "unidade_origem";
		return this.builderMapIntInt(category);
	}
	
	@Override
	public Map<Integer, Integer> getQuantityProcessPerSubjectList() throws DatabaseException {
		String category = "tipo_material";
		return this.builderMapIntInt(category);
	}
	
	private Map<Integer, Integer> builderMapIntInt(String categoryColumn) throws DatabaseException{
		Connection connection = null;
		PreparedStatement statement = null;
		ResultSet resultSet = null;
		
		String query = "SELECT COUNT(id) AS qtde, " + categoryColumn +" FROM processos_compra "
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

}
