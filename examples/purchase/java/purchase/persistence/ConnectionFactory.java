/**
 * 
 */
package purchase.persistence;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

import persistence.exception.DatabaseException;

public class ConnectionFactory {
	
	public static Connection getConnection() throws DatabaseException {
		String driver = "jdbc:mysql://localhost/docmanager";
		String user = "root";
		String pass = System.getenv("DATABASE_PASSWORD");
		
		try {
			return DriverManager.getConnection(driver,user,pass);
		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível estabelecer conexão com o Banco de Dados.", e);
		}		
		
	}
	
	public static void closeConnection(Connection connection) throws DatabaseException {
		
		try {
			if(connection!=null) {
				connection.close();
			}
			
		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível encerrar conexão com o Banco de Dados.", e);
		}
	}
	
	public static void closeConnection(Connection connection, PreparedStatement statement) throws DatabaseException {
		closeConnection(connection);
		
		try {
			if(statement != null) {
				statement.close();
			}
			
		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível destruir o statement construído.", e);

		}
	}
	
	public static void closeConnection(Connection connection, PreparedStatement statement, ResultSet resultSet) throws DatabaseException {
		closeConnection(connection, statement);
		
		try {
			if(resultSet!=null) {
				resultSet.close();
			}
			
		} catch (SQLException e) {
			throw new DatabaseException("Não foi possível destruir o Result Set.", e);

		}
	}
}
