import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import business.exception.ValidationException;
import business.model.Interested;
import business.model.Organization;
import business.model.Process;
import business.model.Situation;
import business.model.Subject;
import health.model.HealthInterested;
import health.model.HealthOrganization;
import health.model.HealthProcess;
import health.model.HealthSituation;
import health.model.HealthSubject;
/**
 * 
 * @author Allan
 *
 */
@RunWith(value = Parameterized.class)
public class HealthProcessTest {
	@Parameters
	public static Collection <Object[]> data(){
		return Arrays.asList(new Object[][] {
			{false, "00000010110145", new HealthInterested("John Doe", "12345678910", "8484848484"), HealthSubject.NULL, HealthOrganization.AGU, HealthSituation.AGENDEXT, ""},
			{false, "00000010110141", new HealthInterested("John Doe", "12345678910", "8484848484"), HealthSubject.APO, HealthOrganization.NULL, HealthSituation.CONCLUIDO, ""},
			{false, "00000010110143", new HealthInterested("John Doe", "12345678910", "8484848484"), HealthSubject.APO, HealthOrganization.CGU, HealthSituation.NULL, ""},
			{false, "000000101101430", new HealthInterested("John Doe", "12345678910", "8484848484"), HealthSubject.APO, HealthOrganization.CGU, HealthSituation.AGENDEXT, ""},
			{true, "a1234567", new HealthInterested("John Doe", "12345678910", "8484848484"), HealthSubject.APO, HealthOrganization.CGU, HealthSituation.AGENDEXT, ""},
			{true, "1112", new HealthInterested("John Doe", "12345678910", "8484848484"), HealthSubject.APO, HealthOrganization.CGU, HealthSituation.AGENDEXT, ""},
		});
	}
	
	private boolean oficio;
	private String numero;
	private Interested interessado;
	private Subject assunto;
	private Organization orgao;
	private Situation situacao;
	private String observacao;

	public HealthProcessTest(boolean oficio, String numero, Interested interessado, Subject assunto, Organization orgao, Situation situacao, String observacao) {
		this.oficio = oficio;
		this.numero = numero;
		this.interessado = interessado;
		this.assunto = assunto;
		this.orgao = orgao;
		this.situacao = situacao;
		this.observacao = observacao;
	}
	
	@Test(expected = ValidationException.class)
	public void creationTest() throws ValidationException {
		
		Process p = new HealthProcess(oficio, numero, interessado, orgao, assunto, situacao, observacao);
		p.validate();
	}
}