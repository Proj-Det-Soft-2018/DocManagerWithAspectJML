/**
 * 
 */
package persistence;

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
import business.model.HealthInterested;
import business.model.HealthProcess;
import business.model.HealthProcessSearch;
import business.model.HealthSituation;
import business.model.Interested;
import business.model.Process;
import business.model.Search;
import persistence.exception.DatabaseException;

/**
 * @author clarissa - clahzita@gmail.com
 * @since 01/04/2018
 */
public class HealthProcessDaoJDBC implements ProcessDao{
	
	@Override
	public void save(Process process) throws DatabaseException, ValidationException {
		//Antes de salvar verificar os campos que nao podem ser nulos
		HealthProcess healthProcess = (HealthProcess)process;
		this.checkDuplicate(healthProcess.getNumber());
		
		
		String sql = "INSERT INTO processos"
					+ "(eh_oficio,numero,interessado_id,"
                	+ "assunto,situacao,orgao_origem,"
                	+ "observacao,data_entrada)"
                	+ " values (?,?,?,?,?,?,?,?)";
		
		Connection connection = null;
		PreparedStatement statement=null;
		try {
			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement(sql);
			
			statement.setBoolean(1, healthProcess.isOficio());
			statement.setString(2, healthProcess.getNumber());
			statement.setLong(3, healthProcess.getIntersted().getId());
			statement.setInt(4, healthProcess.getSubject().getId());
			statement.setInt(5, healthProcess.getSituation().getId());
			statement.setInt(6, healthProcess.getOriginEntity().getId());
			statement.setString(7, healthProcess.getObservation());
			
			//Definindo data de entrada no banco de dados
			LocalDateTime date = LocalDateTime.now();
			healthProcess.setRegistrationDate(date);
			
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
	
	
	@Override
	public void update(Process process) throws DatabaseException {
		
		HealthProcess healthProcess = (HealthProcess)process;
		
		String query = "UPDATE processos SET "
					+ "numero=?, interessado_id=?, assunto=?,"
					+ "situacao=?, orgao_origem=?, observacao=?,"
					+ "eh_oficio=?"
					+ " WHERE id=?";
		
		Connection connection = null;
		PreparedStatement statement=null;
		
		try {
			
			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement(query);
			statement.setString(1, healthProcess.getNumber());
			statement.setLong(2, healthProcess.getIntersted().getId());
			statement.setInt(3, healthProcess.getSubject().getId());
			statement.setInt(4, healthProcess.getSituation().getId());
			statement.setInt(5, healthProcess.getOriginEntity().getId());
			statement.setString(6, healthProcess.getObservation());
			statement.setBoolean(7, healthProcess.isOficio());
			
			//setando id do processo a ser modificado
			statement.setLong(8, healthProcess.getId());
			
			
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
			statement = connection.prepareStatement("DELETE FROM processos WHERE id=?");
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
		int situationId = HealthSituation.CONCLUIDO.getId();
		String sql = "WHERE situacao != "+situationId+
		             " ORDER BY data_entrada ASC" +
		             " LIMIT 50";
		List<Process> intermediaryList = pullProcessList(sql);
		if (intermediaryList.size() < 50) {
		    sql = "WHERE situacao = "+situationId+
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
						+ "FROM processos p "
						+ "INNER JOIN interessados i "
						+ "ON p.interessado_id=i.id "
						+ whereStament;
		
		List<Process> processList = new ArrayList<>();
		
		try {
			connection = ConnectionFactory.getConnection();
			
			statement = connection.prepareStatement(query);
			
			resultSet = statement.executeQuery();
			
			while(resultSet.next()) {
				
				//criando objeto Interessado
				Interested interested = new HealthInterested(
						resultSet.getLong("interessado_id"),
						resultSet.getString("nome"),
						resultSet.getString("cpf"),
						resultSet.getString("contato"));
				
				//criando o objeto Processo
				HealthProcess process = new HealthProcess(
						resultSet.getLong("id"),
						resultSet.getBoolean("eh_oficio"),
						resultSet.getString("numero"),
						resultSet.getString("observacao"));
				process.setInterested(interested);
				
				//falta resolver unidade destino /orgao_saida, se vai ter ou não
				process.setSubjectById(resultSet.getInt("assunto"));
				process.setOriginEntityById(resultSet.getInt("orgao_origem"));
				process.setSituationById(resultSet.getInt("situacao"));

				
				//Convertendo data entrada de java.sql.Date para LocalDateTime
				Date jdbcRegistrationDate = resultSet.getDate("data_entrada");
				if(jdbcRegistrationDate != null) {
					Timestamp jdbcRegistrationStamp = new Timestamp(jdbcRegistrationDate.getTime());
					LocalDateTime registrationDate = jdbcRegistrationStamp.toLocalDateTime();
					process.setRegistrationDate(registrationDate);
				}
				
				//Convertendo data Saida de java.sql.Date para LocalDateTime
				Date jdbcDispatchDate = resultSet.getDate("data_saida");
				if(jdbcDispatchDate != null) {
					Timestamp jdbcDispatchStamp = new Timestamp(resultSet.getDate("data_saida").getTime());
					LocalDateTime dispatchDate = jdbcDispatchStamp.toLocalDateTime();
					process.setDispatchDate(dispatchDate);
				}
				
				processList.add(process);
			
			}
		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível buscar o processo no Banco.", e);
		} catch (ValidationException e) {
			throw new DatabaseException("Banco corrompido!", e);
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

	public List<Process> searchAll(Search searchData) throws DatabaseException {
	    HealthProcessSearch search = (HealthProcessSearch) searchData;
		StringBuilder sql = new StringBuilder("WHERE ");
		final String AND = " AND ";
		
		String number = search.getNumber();
		if (number != null && !number.equalsIgnoreCase("")) {
			sql.append("numero LIKE '"+number+"' AND ");
		}
		
		String name = search.getName();
		if (name != null && !name.equalsIgnoreCase("")) {
			sql.append("nome LIKE '%"+name+"%' AND ");
		}
		
		String cpf = search.getCpf();
		if (cpf != null && !cpf.equalsIgnoreCase("")) {
			sql.append("cpf= '"+cpf+"' AND ");
		}
		
		int organizationId = search.getOrganizationId();
		if (organizationId != 0) {
			sql.append("orgao_origem="+organizationId+AND);
		}
		
		int subjectId = search.getSubjectId();
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
	
	//Methods to resolve statistic solutions
	@Override
	public Map<Integer, ArrayList<Integer>> getQuantityProcessPerMonthYearList() throws DatabaseException {
		String query = "SELECT COUNT(id), EXTRACT(year from data_entrada) as ano, EXTRACT(month from data_entrada) AS mes "
						+ "FROM processos "
						+ "GROUP BY ano, mes ORDER BY ano, mes";
		
		return this.builderMapIntArrayInt(query);
	}
	
	@Override
	public Map<Integer, ArrayList<Integer>> getQuantityProcessPerMonthFromLastYearList() throws DatabaseException {
		String query = "SELECT COUNT(id), EXTRACT(year from data_entrada) as ano, EXTRACT(month from data_entrada) AS mes "
						+ "FROM (SELECT * FROM processos WHERE data_entrada BETWEEN CURDATE() - INTERVAL 1 YEAR AND CURDATE() ) AS processosUltimoAno "
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
		String category = "orgao_origem";
		return this.builderMapIntInt(category);
	}
	
	@Override
	public Map<Integer, Integer> getQuantityProcessPerSubjectList() throws DatabaseException {
		String category = "assunto";
		return this.builderMapIntInt(category);
	}
	
	private Map<Integer, Integer> builderMapIntInt(String categoryColumn) throws DatabaseException{
		Connection connection = null;
		PreparedStatement statement = null;
		ResultSet resultSet = null;
		
		String query = "SELECT COUNT(id) AS qtde, " + categoryColumn +" FROM processos "
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
	
	/**
	 *  Método procura no banco se tem outro processo com o mesmo número. Se tem, o registro deve
	 *  estar com a situação definida como concluída. Caso contrário, pede confirmação do 
	 *  usuário para modificar situacao do registro antigo como concluido.
	 *  
	 * @param numero Numero do processo que está sendo inserido.
	 * @throws ValidationException 
	 * @throws DatabaseException 
	 */
	private void checkDuplicate(String numero) throws ValidationException, DatabaseException {
		List<Process> duplicados = this.searchByNumber(numero);
		if(duplicados != null && !duplicados.isEmpty()) {
			//verifica se a situacao dos processos encontrados estao como concluido
			for (Process processo : duplicados) {
				HealthProcess healthProcess = (HealthProcess)processo;
				if(!(healthProcess.getSituation().getId()==HealthSituation.CONCLUIDO.getId()) ) {
					//TODO Tem que remover isso daqui
					throw new ValidationException("Existe outro processo cadastrado com situação não concluída");
				}				
			}			
		}		
	}



}
