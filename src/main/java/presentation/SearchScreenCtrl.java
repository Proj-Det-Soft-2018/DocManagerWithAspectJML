package presentation;

import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.ResourceBundle;
import org.apache.log4j.Logger;
import business.exception.ValidationException;
import business.model.Process;
import business.model.Search;
import business.service.Observer;
import business.service.ProcessService;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.TableView;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;
import persistence.exception.DatabaseException;
import presentation.utils.StringConstants;
import presentation.utils.widget.ExceptionAlert;

/**
 * Classe abstrata para controlador da tela de busca de de objetos que implementem a interface
 * {@code Process} que utiliza objetos que, por sua vez, implementem a interface {@code Search}.
 * Como é um dos pontos flexíveis do framework, o desenvolvedor deve implementar seus métodos
 * abstratos para obter um controlador para a tela.
 * 
 * @author hugo
 * 
 * @see business.model.Process
 * @see business.model.Search
 */
/**
 * @author hugo
 *
 */
public abstract class SearchScreenCtrl implements Initializable, Observer {

  private Logger logger;

  private ControllerFactory controllerFactory;
  private ProcessService processService;

  private Process selectedProcess;
  private Search ultimaBusca;

  @FXML
  private Node root;

  @FXML
  protected TableView<Process> tableResultados;

  @FXML
  private Button btnVerEditar;

  @FXML
  private Button btnCertidaoPdf;

  @FXML
  private Button btnApagar;

  /**
   * Método estático para exibição da tela para busca de objetos que implementem a interface
   * {@code Process}. Caso ocorra algum erro na montagem da tela o método exibirá um um
   * {@code ExceptionAlert}.
   * 
   * @param ownerWindow Tela que chamou este método.
   * @param controller Controlador da tela.
   * 
   * @see business.model.Process
   * @see presentation.utils.widget.ExceptionAlert
   */
  public static void showSearchScreen(Window ownerWindow, SearchScreenCtrl controller) {
    try {
      FXMLLoader loader = new FXMLLoader(controller.getFxmlPath());
      loader.setController(controller);
      Parent rootParent = loader.load();

      Stage searchScreen = new Stage();
      searchScreen.initModality(Modality.WINDOW_MODAL);
      searchScreen.initOwner(ownerWindow);
      searchScreen.setTitle(StringConstants.TITLE_SEARCH_SCREEN.getText());
      searchScreen
      .setScene(new Scene(rootParent, rootParent.prefWidth(-1), rootParent.prefHeight(-1)));

      searchScreen.show();
    } catch (IOException e) {
      ExceptionAlert.show("Não foi possível gerar a tela!", ownerWindow);
      Logger.getLogger(SearchScreenCtrl.class).error(e.getMessage(), e);
    }
  }
  
  /**
   * Construtor para objetos {@code SearchScreenCtrl}
   * 
   * @param controllerFactory Fábrica de Controladores
   * @param processService Serviço de Processos
   * @param logger {@code org.apache.log4j.Logger} para efetuação de logs
   */
  public SearchScreenCtrl(ControllerFactory controllerFactory, ProcessService processService,
      Logger logger) {
    this.controllerFactory = controllerFactory;
    this.processService = processService;
    this.logger = logger;
    selectedProcess = null;
    ultimaBusca = null;
  }

  /* (non-Javadoc)
   * @see javafx.fxml.Initializable#initialize(java.net.URL, java.util.ResourceBundle)
   */
  @Override
  public void initialize(URL location, ResourceBundle resources) {
    processService.attach(this);
    configureForm();
    configureTable();
    Platform.runLater(this::configureClosure);
  }

  /* (non-Javadoc)
   * @see business.service.Observer#update()
   */
  @Override
  public void update() {
    if (this.ultimaBusca != null) {
      List<Process> resultado = null;
      try {
        resultado = this.processService.searchAll(ultimaBusca);
      } catch (DatabaseException e) {
        ExceptionAlert.show("ERRO! Contate o administrador do sistema.",
            root.getScene().getWindow());
        logger.error(e.getMessage(), e);
      } catch (ValidationException e) {
        ExceptionAlert.show(e.getMessage(), root.getScene().getWindow());
      }
      updateTable(resultado);
    }
  }

  /**
   * Método para configuração de captura de eventos da tabela de processos.
   */
  private void configureTable() {
    // eventHandle para detectar o processo selecionado
    tableResultados.getSelectionModel().selectedItemProperty()
    .addListener((observavel, selecionandoAnterior, selecionadoNovo) -> {
      this.selectedProcess = selecionadoNovo;
      this.btnVerEditar.setDisable(selecionadoNovo != null ? false : true);
      this.btnCertidaoPdf.setDisable(selecionadoNovo != null ? false : true);
      this.btnApagar.setDisable(selecionadoNovo != null ? false : true);
    });
    // chama o método abstrato para configurar as colunas
    configureColumns();
  }

  /**
   * Método para execução do evento de clique no botão "Buscar", consiste em montar um objeto que
   * implemente a interface {@code Search} com os dados do formulário da aplicação e então efetuar
   * uma busca no serviço de processos. Caso não haja inserção de dados ou problema no acesso ao
   * banco o método exibirá um {@code ExceptionAlert}.
   * 
   * @see business.model.Search
   * @see presentation.utils.widget.ExceptionAlert
   */
  @FXML
  private void search() {

    Search search = mountSearch();
    try {
      List<Process> resultado = processService.searchAll(search);
      ultimaBusca = search;
      updateTable(resultado);
    } catch (ValidationException ve) {
      ExceptionAlert.show(ve.getMessage(), root.getScene().getWindow());
    } catch (DatabaseException e) {
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
      logger.error(e.getMessage(), e);
    }
  }

  /**
   * Método para execução do evento do botão de voltar. Fecha a tela.
   */
  @FXML
  private void closeWindow() {
    Stage window = (Stage) this.root.getScene().getWindow();
    if (window != null)
      window.close();
  }

  /**
   * Configura o fechamento da tela para que, quando ocorra, desvincule este controlador da lista de
   * observadores do serviço de Processos.
   */
  private void configureClosure() {
    root.getScene().getWindow().setOnHidden(event -> processService.dettach(this));
  }
  
  /**
   * A atualiza a exibição na tabela com a lista passada por parâmetro.
   *
   * @param processList Lista de processos para exibição
   */
  private void updateTable(List<Process> processList) {
    tableResultados.getItems().setAll(processList);
  }

  /**
   * Método para execução do evento de clique no botão "Ver/Editar", consiste em mostrar a tela de
   * edição de processos para um processo selecionado na tabela.
   */
  @FXML
  private void showProcessEditScreen() {
    ProcessEditCtrl.showProcessEditScreen(root.getScene().getWindow(),
        controllerFactory.createProcessEditCtrl(), selectedProcess);
  }

  /**
   * Método para execução do evento de clique no botão "Apagar", consiste em mostrar um dialog para
   * confimação com senha para exclusão do processo selecionado.
   */
  @FXML
  private void showDeleteDialog() {
    DeleteDialogCtrl.showDeleteDialog(root.getScene().getWindow(),
        controllerFactory.createDeleteDialogCtrl(), selectedProcess);
  }

  /**
   * Método para execução do evento de clique no botão "Certidão Pdf", consiste em mostrar a tela de
   * visualização de Pdf com o arquivo preparado com o processo selecionado.
   */
  @FXML
  private void showPdfViewer() {
    PdfViewerCtrl.showPdfViewer(root.getScene().getWindow(),
        controllerFactory.createPdfViewerCtrl(), selectedProcess);
  }

  /**
   * Método que deve ser implementado para inicializar o formulário, preenchendo os choice-boxes e
   * configurando eventos.
   */
  protected abstract void configureForm();

  /**
   * Método que deve ser implementado para criação de um objeto que implementa a interface 
   * {@code Search} de acordo com a aplicação.
   * 
   * @return Novo objeto de busca
   * 
   * @see business.model.Search
   */
  protected abstract Search mountSearch();

  /**
   * Método abstrato que deve ser implementado para configurar a forma de preenchimento das linhas
   * da tabela com os objetos específicos de cada aplicação.
   */
  protected abstract void configureColumns();

  /**
   * Método que dever ser implementado para obtenção do caminho ({@code java.net.URL} para o arquivo
   * .fxml.
   * 
   * @return Caminho para o arquivo.
   */
  public abstract URL getFxmlPath();
}
