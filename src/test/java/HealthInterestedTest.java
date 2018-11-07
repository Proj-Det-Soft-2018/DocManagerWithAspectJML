import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import business.exception.ValidationException;
import business.model.HealthInterested;
import business.model.Interested;

@RunWith(value = Parameterized.class)
public class HealthInterestedTest {
	
	@Parameters
	public static Collection <Object[]> data(){
		return Arrays.asList(new Object[][] {
			{null, "12345678910", "84999999999"},
			{"teste dois", "12345678910", null},
			{"", "12345678910", "84999999999"},
			{"teste1","12345678910", "8433334444"},
			{"teste","12345678910", "8433"},
			{"teste","1234567891", "8433334444"},
			{"teste","123456789101", "8433334444"},
		});
	}
	
	private String nome;
	private String cpf;
	private String contato;
	
	public HealthInterestedTest(String nome, String cpf, String contato) {
		this.nome = nome;
		this.cpf = cpf;
		this.contato = contato;
	}



	@Test(expected = ValidationException.class)
	public void creationTest() throws ValidationException {
		Interested i = new HealthInterested(nome, cpf, contato);
		i.validate();
	}

}