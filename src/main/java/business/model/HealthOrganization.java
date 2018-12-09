package business.model;

import java.util.ArrayList;
import java.util.List;

import business.model.Organization;

public enum HealthOrganization implements Organization {

  NULL(null),
  UFRN("Universidade Federal do Rio Grande do Norte"),
  DPF("Departamento de Polícia Federal"),
  MTE("Ministério Do Trabalho e Emprego"),
  DPRF("Departamento de Policia Rodoviaria Federal"),
  FUNAI("Fundação Nacional do Índio"),
  MAPA("Ministério da Agricultura, Pecuaria e Abastecimento"),
  MF("Ministério da Fazenda"),
  MJ("Ministério da Justiça"),
  MPOG("Ministério do Planejamento Desenvolvimento e Gestão"),
  IPHAN("Instituto do Patrimônio Histórico e Artístico Nacional"),
  UFERSA("Universidade Federal Uural do Semi-Árido"),
  FUNASA("Fundação Nacional de Saúde"),
  DNPM("Departamento Nacional de Produção Mineral"),
  ANVISA("Agência Nacional de Vigilância Sanitária"),
  DPU("Defensoria Pública da União"),
  DNIT("Departamento Nacional de Infraestrutura de Transportes"),
  AGU("Advocacia-Geral da União"),
  MCTI("Ministério da Ciência, Tecnologia, Inovações e Comunicações"),
  IBAMA("Instituto Brasileiro do Meio Ambiente e dos Recursos Naturais Renováveis"),
  INCRA("Instituto Nacional de Colonização e Reforma Agrária"),
  DNOCS("Departamento Nacional de Obras Contra as Secas"),
  ICMBIO("Instituto Chico Mendes de Conservação da Biodiversidade"),
  IBGE("Instituto Brasileiro de Geografia e Estatística"),
  CGU("Ministério da Transparência e Controladoria-Geral da União");

  private /*@ spec_public nullable @*/ String fullName; // in orgFullName;
  //@ protected represents orgFullName <- fullName;

  /*@ assignable this.fullName;
	  @ ensures this.fullName == fullName;
	  @*/
  HealthOrganization(/*@ non_null @*/String fullName) {
    this.fullName = fullName;
  }

  @Override
  public String getFullName() {
    return fullName;
  }

  @Override
  public String getInitials(){
    return name();
  }

  @Override
  public int getId() {
    return ordinal();
  }

  /*@	ensures \result.size() == 24;
	  @	ensures \result.contains(NULL) == false;
	  @ ensures (\forall int i;
	  @             0 <= i && i < \result.size();
	  @             \result.get(i) != null && !((Organization)\result.get(i)).getInitials().isEmpty() &&
    @                 !((Organization)\result.get(i)).getFullName().isEmpty());
	  @*/
  public static List<Organization> getAll() {
    List<Organization> organizationList = new ArrayList<>();
    for(HealthOrganization organization : HealthOrganization.values()) {
      organizationList.add(organization);
    }
    organizationList.remove(0);
    return organizationList;
  }

  /*@ requires id >=0 && id < 25;
	  @   ensures \result != null;
	  @*/
  public static HealthOrganization getOrganizationById(int id){
    return HealthOrganization.values()[id];
  }
}
