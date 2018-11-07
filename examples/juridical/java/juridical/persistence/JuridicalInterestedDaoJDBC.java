package juridical.persistence;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

import business.model.Interested;
import business.model.Search;
import juridical.model.JuridicalInterested;
import juridical.model.JuridicalInterestedSearch;
import persistence.InterestedDao;
import persistence.exception.DatabaseException;

public class JuridicalInterestedDaoJDBC implements InterestedDao {

	@Override
	public void save(Interested interested) throws DatabaseException {
		JuridicalInterested juridicalInterested = (JuridicalInterested)interested;
		String sql = "INSERT INTO inventariante " +
				"(nome,cpf,contato,idade,email)" +
				" VALUES (?,?,?,?,?)";

		Connection connection = null;
		PreparedStatement statement = null;
		try {
			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement(sql);
			statement.setString(1,juridicalInterested.getName());
			statement.setString(2,juridicalInterested.getCpf());
			statement.setString(3,juridicalInterested.getContact());
			statement.setInt(4,juridicalInterested.getIdade());
			statement.setString(5,juridicalInterested.getEmail());

			statement.executeUpdate();

		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível salvar o interessado no Banco de Dados.", e);
		}
		finally {
			ConnectionFactory.closeConnection(connection, statement);
		}

	}

	@Override
	public void update(Interested interested) throws DatabaseException {
		JuridicalInterested juridicalInterested = (JuridicalInterested)interested;
		String sql = "UPDATE inventariante " +
				"SET nome=?, cpf=?, contato=?, idade=?, email=? " +
				"WHERE id=?";
		Connection connection = null;
		PreparedStatement statement = null;
		try {
			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement(sql);

			statement.setString(1, juridicalInterested.getName());
			statement.setString(2, juridicalInterested.getCpf());
			statement.setString(3, juridicalInterested.getContact());
			statement.setInt(4, juridicalInterested.getIdade());
			statement.setString(5, juridicalInterested.getEmail());
			statement.setLong(6, juridicalInterested.getId());

			statement.executeUpdate();

		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível atualizar o interessado no Banco de Dados.", e);
		}finally {
			ConnectionFactory.closeConnection(connection, statement);
		}

	}

	@Override
	public void delete(Interested interested) throws DatabaseException {
		Connection connection = null;
		PreparedStatement statement = null;
		try {
			connection = ConnectionFactory.getConnection();
			statement = connection.prepareStatement("DELETE FROM inventariante WHERE id=?");
			statement.setLong(1, interested.getId());
			statement.executeUpdate();

		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível deletar o processo do Banco de Dados.", e);
		}finally {
			juridical.persistence.ConnectionFactory.closeConnection(connection, statement);
		}

	}

	@Override
	public Interested search(Search searchData) throws DatabaseException {
		JuridicalInterestedSearch search = (JuridicalInterestedSearch) searchData;
		Connection connection = null;
		PreparedStatement statement = null;
		ResultSet resultSet = null;

		try {
			connection = ConnectionFactory.getConnection();

			statement = connection.prepareStatement("SELECT * FROM inventariante WHERE cpf=?");
			statement.setString(1, search.getCpf());

			resultSet = statement.executeQuery();

			JuridicalInterested interested = null;

			if(resultSet.next()) {
				//criando o objeto Interessado
				interested = new JuridicalInterested();
				interested.setId(resultSet.getLong("id"));
				interested.setName(resultSet.getString("nome"));
				interested.setCpf(resultSet.getString("cpf"));
				interested.setIdade(resultSet.getInt("idade"));
				interested.setContact(resultSet.getString("contato"));
				interested.setEmail(resultSet.getString("email"));
			}

			return interested;

		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível recuperar o interessado pelo CPF", e);
		}finally {
			ConnectionFactory.closeConnection(connection, statement, resultSet);
		}
	}

}
