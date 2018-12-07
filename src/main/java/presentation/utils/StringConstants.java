package presentation.utils;

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
	
	private /*@ spec_public nullable @*/ String text;

	private StringConstants(String text) {
		this.text = text;
	}

	public String getText() {
    return text;
  }
}
