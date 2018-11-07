package presentation.utils;

/**
 * Classe de enumeração para referencia às constantes {@code String} utilizadas pelas classes
 * controladores do pacote {@code presentation}.  
 * 
 * @author hugo
 */
public enum StringConstants {
	TITLE_APPLICATION ("DocManager"),
	TITLE_PDF_VIEWER_SCREEN ("Certidão"),
	TITTLE_PDF_SAVE_SCREEN ("Salvar Documento"),
	TITLE_CREATE_PROCESS_SCREEN ("Novo Processo / Ofício"),
	TITLE_EDIT_PROCESS_SCREEN ("Editar Processo"),
	TITLE_CREATE_INTERESTED_SCREEN ("Novo Interessado"),
	TITLE_EDIT_INTERESTED_SCREEN ("Editar Interessado"),
	TITLE_SEARCH_SCREEN ("Buscar Processos / Ofícios"),
	TITLE_STATISTICS_SCREEN ("Gráficos Estatísticos"),
	TITLE_DELETE_DIALOG ("Autorização"),
	
	ERROR_PASSWORD ("Usuário ou Senha Incorretos!");
	
	private String text;

	private StringConstants(String text) {
		this.text = text;
	}

	public String getText() {
    return text;
  }
}
