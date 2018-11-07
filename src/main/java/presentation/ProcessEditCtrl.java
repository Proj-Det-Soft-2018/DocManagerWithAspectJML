package presentation;

import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;
import org.apache.log4j.Logger;
import business.exception.ValidationException;
import business.model.Interested;
import business.model.Process;
import business.model.Search;
import business.service.InterestedService;
import business.service.Observer;
import business.service.ProcessService;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;
import persistence.exception.DatabaseException;
import presentation.utils.StringConstants;
import presentation.utils.widget.ExceptionAlert;

 /**
 * Classe abstrata para controlador da tela de edição de objetos que implementem a interface
 * {@code Process}. Como é um dos pontos flexíveis do framework, o desenvolvedor deve implementar
 * seus métodos abstratos para obter um controlador para tela de edição de Processos.
 * 
 * @author hugo
 * 
 * @see business.model.Process
 */
public abstract class ProcessEditCtrl implements Initializable, Observer {

  private Logger logger;

  private ProcessService processService;
  private InterestedService interestedService;
  private ControllerFactory controllerFactory;

  protected Process originalProcess;
  protected Interested interested;

  @FXML
  private Node root;

  /**
   * Método estático para exibição da tela de edição de objetos que extendem a interface 
   * {@code Process}. Caso ocorra algum erro na montagem da tela este método exibirá um um {@code ExceptionAlert}.
   * 
   * @param ownerWindow Tela que chamou este método.
   * @param controller Controlador da tela.
   * @param process Processo selecionado para edição.
   * 
   * @see business.model.Process
   * @see presentation.utils.widget.ExceptionAlert
   */
  public static void showProcessEditScreen(Window ownerWindow, ProcessEditCtrl controller,
      Process process) {
    try {
      FXMLLoader loader = new FXMLLoader(controller.getFxmlPath());
      controller.setOriginalProcess(process);
      loader.setController(controller);
      Parent rootParent = loader.load();

      Stage processEditScreen = new Stage();
      processEditScreen.initModality(Modality.WINDOW_MODAL);
      processEditScreen.initOwner(ownerWindow);
      if (process == null) {
        processEditScreen.setTitle(StringConstants.TITLE_CREATE_PROCESS_SCREEN.getText());
      } else {
        processEditScreen.setTitle(StringConstants.TITLE_EDIT_PROCESS_SCREEN.getText());
      }
      processEditScreen
          .setScene(new Scene(rootParent, rootParent.prefWidth(-1), rootParent.prefHeight(-1)));

      processEditScreen.show();
    } catch (IOException e) {
      ExceptionAlert.show("Não foi possível gerar a tela!", ownerWindow);
      Logger.getLogger(ProcessEditCtrl.class).error(e.getMessage(), e);
    }
  }

  /**
   * Construtor para objetos {@code ProcessEditCtrl}.
   * 
   * @param processService Serviço de Processos
   * @param interestedService Serviço de Interessados
   * @param controllerFactory Fábrica de Controladores
   * @param logger {@code Logger} para efetuação de logs.
   * 
   * @see code org.apache.log4j.Logger
   */
  protected ProcessEditCtrl(ProcessService processService, InterestedService interestedService,
      ControllerFactory controllerFactory, Logger logger) {
    this.processService = processService;
    this.interestedService = interestedService;
    this.controllerFactory = controllerFactory;
    this.logger = logger;
    this.originalProcess = null;
    this.interested = null;
  }

  private void setOriginalProcess(Process originalProcess) {
    this.originalProcess = originalProcess;
  }

  /* (non-Javadoc)
   * @see javafx.fxml.Initializable#initialize(java.net.URL, java.util.ResourceBundle)
   */
  @Override
  public void initialize(URL location, ResourceBundle resources) {
    interestedService.attach(this);
    initializeForm();
    Platform.runLater(this::configureClosure);
  }

  /* (non-Javadoc)
   * @see business.service.Observer#update()
   */
  @Override
  public void update() {
    searchInterestedByUniqueKey();
  }

  /**
   * Método para execução do evento de clique no botão "Buscar". Busca um objeto de Interessado a
   * partir da chave única fornecida no formulário da tela, e então mostra suas informações na tela
   * ou, caso não seja encontrado um objeto para a chave fornecida, mostra uma nova tela de edição
   * de interessados para criação do objeto.
   */
  @FXML
  private void searchInterestedByUniqueKey() {
    try {
      this.interested = interestedService.search(mountSearch());
      if (interested == null) {
        this.showInterestedCreateScreen();
      } else {
        this.fillInterestedField();
      }
    } catch (ValidationException ve) {
      ExceptionAlert.show(ve.getMessage(), root.getScene().getWindow());
    } catch (DatabaseException e) {
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
      logger.error(e.getMessage(), e);
    }
  }

  /**
   * Cria um novo interessado e mostra a tela de edição para preenchimento de seus dados.
   */
  @FXML
  private void showInterestedCreateScreen() {
    Interested newInterested = createInterested();
    InterestedEditCtrl.showIntestedEditScreen(root.getScene().getWindow(),
        controllerFactory.createInterestedEditCtrl(), newInterested);
  }

  /**
   * Método para execução do evento de clique no botão "Editar". Mostra a tela de edição para o
   * interessado exibido pelo formulário. 
   */
  @FXML
  protected void showInterestedEditScreen() {
    InterestedEditCtrl.showIntestedEditScreen(root.getScene().getWindow(),
        controllerFactory.createInterestedEditCtrl(), interested);
  }

  /**
   * Método para execução do evento de clique no botão "Limpar". Limpa as informações referentes ao
   *  interessado mostradas na tela.
   */
  @FXML
  protected void clearInterested() {
    interested = null;
    clearInterestedField();
  }

  /**
   * Configura o fechamento da tela para que, quando ocorra, desvincule este controlador da lista de
   * observadores dos serviços de Processos e de Interessados.
   */
  private void configureClosure() {
    root.getScene().getWindow().setOnHidden(event -> this.interestedService.dettach(this));
  }

  /**
   * Método para execução do evento do botão de cancelar ou quando salvar um processo. Fecha a tela.
   */
  @FXML
  private void closeWindow() {
    Stage janela = (Stage) this.root.getScene().getWindow();
    if (janela != null)
      janela.close();
  }

  /**
   * Método para execução do evento do botão de confirmação de edição. Nele, obtên-se os dados
   * inseridos no formulários, monta um process e faz-se a tentativa de salvar no banco, fechando a 
   * tela em caso de confirmação ou exibindo um {@code ExceptionAlert} caso de usuário cometa algum
   * erro no preenchimento do objeto ou um genérico {@code ExceptionAlert} em caso de falha no 
   * banco.
   */
  @FXML
  private void save() {
    Process editedProcess = mountProcess();
    try {
      if (originalProcess == null) {
        processService.save(editedProcess);
      } else {
        editedProcess.setId(originalProcess.getId());
        processService.update(editedProcess);
      }
      this.closeWindow();
    } catch (ValidationException ve) {
      ExceptionAlert.show(ve.getMessage(), root.getScene().getWindow());
    } catch (DatabaseException e) {
      ExceptionAlert.show("ERRO! Contate o administrador do sistema", root.getScene().getWindow());
      logger.error(e.getMessage(), e);
    }
  }

  
  /**
   * Método que deve ser implementado para inicializar o formulário, preenchendo os choice-boxes e
   * configurando eventos.
   */
  protected abstract void initializeForm();

  /**
   * Método que deve ser implementado para criação de um objeto que implementa a interface 
   * {@code Interested} de acordo com a aplicação.
   * 
   * @return Novo objeto interessado.
   * 
   * @see business.model.Interested
   */
  protected abstract Interested createInterested();

  /**
   * Método que deve ser implementado para montar um novo objeto que implementa a interface 
   * {@code Search} de acordo com a aplicação.
   * 
   * @return Novo objeto com as informações de busca.
   * 
   * @see business.model.Search
   */
  protected abstract Search mountSearch();

  /**
   * Método que deve ser implementado para preenchimento dos campos específicos para interessado no
   * formulário.
   */
  protected abstract void fillInterestedField();

  /**
   * Método que deve ser implementado para limpar os campos específicos para interessado no formu-
   * lário.
   */
  protected abstract void clearInterestedField();

  /**
   * Método que deve ser implementado para criação de um objeto que implementa a interface 
   * {@code Process} de acordo com a aplicação.
   * 
   * @return Novo objeto de processo
   * 
   * @see business.model.Process
   */
  protected abstract Process mountProcess();

  /**
   * Método que deve ser implementado para obtenção do caminho para o arquivo .fxml da tela de edi-
   * ção de processos.
   */
  public abstract URL getFxmlPath();
}
