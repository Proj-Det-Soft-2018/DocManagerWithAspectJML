package presentation;

import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;
import org.apache.log4j.Logger;
import business.exception.ValidationException;
import business.model.Interested;
import business.service.InterestedService;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.layout.Pane;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;
import persistence.exception.DatabaseException;
import presentation.utils.StringConstants;
import presentation.utils.widget.ExceptionAlert;

/**
 * Classe abstrata para controlador da tela de edição de objetos que implementem a interface
 * {@code Interested}. Como é um dos pontos flexíveis do framework, o desenvolvedor deve implementar
 * seus métodos abstratos para obter um controlador para tela de edição de Interessados.
 * 
 * @author hugo
 */
public abstract class InterestedEditCtrl implements Initializable {
  private Logger logger;

  protected Interested interested;
  private InterestedService interestedService;

  /**
   * Referencia ao painel ({@code javafx.scene.layout.Pane} que contêm os elementos da tela.
   */
  @FXML
  protected Pane root;

  /**
   * Método estático para exibição da tela para edição de objetos que implementem a interface
   * {@code Interested}. Caso ocorra algum erro na montagem da tela o método exibirá um um
   * {@code ExceptionAlert}.
   * 
   * @param ownerWindow Tela que chamou este método.
   * @param controller Controlador da tela.
   * @param process Interessado selecionado para edição.
   */
  public static void showIntestedEditScreen(Window ownerWindow, InterestedEditCtrl controller,
      Interested interested) {
    try {
      FXMLLoader loader = new FXMLLoader(controller.getFxmlPath());
      controller.setInterested(interested);
      loader.setController(controller);
      Parent rootParent = loader.load();

      Stage interestedEditScreen = new Stage();
      interestedEditScreen.initModality(Modality.WINDOW_MODAL);
      interestedEditScreen.initOwner(ownerWindow);
      if (interested.getId() == null) {
        interestedEditScreen.setTitle(StringConstants.TITLE_CREATE_INTERESTED_SCREEN.getText());
      } else {
        interestedEditScreen.setTitle(StringConstants.TITLE_EDIT_INTERESTED_SCREEN.getText());
      }

      interestedEditScreen.setScene(controller.getDimensionedScene(rootParent));
      interestedEditScreen.show();
    } catch (IOException e) {
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", ownerWindow);
      Logger.getLogger(InterestedEditCtrl.class).error(e.getMessage(), e);
    }
  }

  /**
   * Construtor que deve ser chamado pelas classes que extendam {@code InterestedEditCtrl}.
   * 
   * @param interestedService Serviço de interessados
   * @param logger {@code org.apache.log4j.Logger} para efetuação de logs.
   */
  protected InterestedEditCtrl(InterestedService interestedService, Logger logger) {
    this.interestedService = interestedService;
    this.logger = logger;
  }

  private void setInterested(Interested interested) {
    this.interested = interested;
  }

  /*
   * (non-Javadoc)
   * 
   * @see javafx.fxml.Initializable#initialize(java.net.URL, java.util.ResourceBundle)
   */
  @Override
  public void initialize(URL location, ResourceBundle resources) {
    populeForm();
  }


  /**
   * Método para execução do evento do botão de confirmação de edição. Nele, obtên-se os dados
   * inseridos no formulários, monta um interessado e faz-se a tentativa de salvar no banco, fechan-
   * do a tela em caso de confirmação ou exibindo um {@code ExceptionAlert} caso de usuário cometa
   * algum erro no preenchimento do objeto ou um genérico {@code ExceptionAlert} em caso de falha no
   * banco.
   */
  @FXML
  private void save() {
    Interested editedIntested = mountInterested();

    try {
      editedIntested.validate();

      if (interested.getId() == null) {
        interestedService.save(editedIntested);
      } else {
        editedIntested.setId(interested.getId());
        interestedService.update(editedIntested);
      }
      this.closeWindow();
    } catch (ValidationException e) {
      ExceptionAlert.show(e.getMessage(), root.getScene().getWindow());
    } catch (DatabaseException e) {
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
      logger.error(e.getMessage(), e);
    }
  }

  /**
   * Método para execução do evento do botão de cancelamento, ou após a edição do interessado. Este
   * método fecha a tela.
   */
  @FXML
  private void closeWindow() {
    Stage janela = (Stage) root.getScene().getWindow();
    if (janela != null)
      janela.close();
  }

  /**
   * Método que dever ser implementado para popular o formário específico de cada aplicação com os
   * dados do objeto {@code Interested} que será editado
   */
  protected abstract void populeForm();

  /**
   * Método que dever ser implementado para montar um objeto {@code Interested} com os dados obtidos
   * do formário específico para cada aplicação.
   * 
   * @return Objeto {@code Interested} com as informações coletadas.
   */
  protected abstract Interested mountInterested();

  /**
   * Método que dever ser implementado para obtenção da cena da tela de edição com as dimensões cor-
   * retas.
   * 
   * @param rootParent {@code javafx.scene.Parent} montado pelo {@code javafx.fxml.FXMLLoader}.
   * @return Cena da tela de edição.
   */
  protected abstract Scene getDimensionedScene(Parent rootParent);

  /**
   * Método que dever ser implementado para obtenção do caminho ({@code java.net.URL} para o arquivo
   * .fxml.
   * 
   * @return Caminho para o arquivo.
   */
  public abstract URL getFxmlPath();
}
