package presentation;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import org.apache.log4j.Logger;
import java.util.ResourceBundle;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.chart.BarChart;
import javafx.scene.chart.CategoryAxis;
import javafx.scene.chart.PieChart;
import javafx.scene.chart.PieChart.Data;
import javafx.scene.chart.XYChart;
import javafx.scene.control.Tooltip;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;
import persistence.exception.DatabaseException;
import presentation.utils.StringConstants;
import presentation.utils.widget.ExceptionAlert;

/**
 * Classe controladora da tela de estatísticas dos processos salvos no sistema. Este controlador 
 * gera a estatística do número de processos realizados no ultimo ano, a sua distribuição pelos me-
 * ses do ano e sua contagem de acordo com os classificadores fornecidos pela aplicação. 
 * 
 * @author clah
 */
public class StatisticsScreenCtrl implements Initializable {

  private static final URL FXML_PATH =
      PdfViewerCtrl.class.getResource("/visions/statistics_screen.fxml");
  private static final Logger LOGGER = Logger.getLogger(StatisticsScreenCtrl.class);

  private StatisticService statisticService;
  private ProcessService processService;
  private ListService listService;

  private ObservableList<String> monthsObsList = FXCollections.observableArrayList();
  private ObservableList<String> lastTwelveMonthsObsList = FXCollections.observableArrayList();

  @FXML
  private Node root;

  // First Tab
  @FXML
  private BarChart<String, Number> bcPerMonthYear;
  @FXML
  private CategoryAxis categoryAxisMonthYear;

  // Second tab
  @FXML
  private BarChart<String, Number> bcLastTwelveMonths;
  @FXML
  private CategoryAxis categoryAxisLastYear;

  // Third tab
  @FXML
  private PieChart pieChart;

  /**
   * Construtor para objetos da classe {@code StatisticsScreenCtrl}.
   * 
   * @param statisticService Serviço que oferece as contagens
   * @param processService Serviço de processos para avaliar se há processos no banco
   * @param listService Serviço de listas para categorização
   */
  public StatisticsScreenCtrl(StatisticService statisticService, ProcessService processService,
      ListService listService) {
    this.statisticService = statisticService;
    this.processService = processService;
    this.listService = listService;
  }

  /**
   * Método estático para exibição da tela de estatísticas de objetos que implementem a interface
   * {@code Process}. Caso ocorra algum erro na montagem da tela o método exibirá um um
   * {@code ExceptionAlert}.
   * 
   * @param ownerWindow Tela que chamou este método.
   * @param controller Controlador da tela.
   * 
   * @see business.model.Process
   * @see presentation.utils.widget.ExceptionAlert
   */
  public static void showStatisticsScreen(Window ownerWindow, StatisticsScreenCtrl controller) {
    try {
      FXMLLoader loader = new FXMLLoader(FXML_PATH);
      loader.setController(controller);
      Parent rootParent = loader.load();

      Stage statisticsScreen = new Stage();
      statisticsScreen.setTitle(StringConstants.TITLE_STATISTICS_SCREEN.getText());
      statisticsScreen.initModality(Modality.WINDOW_MODAL);
      statisticsScreen.initOwner(ownerWindow);
      statisticsScreen
      .setScene(new Scene(rootParent, rootParent.prefWidth(-1), rootParent.prefHeight(-1)));

      statisticsScreen.show();
    } catch (IOException e) {
      ExceptionAlert.show("Não foi possível gerar a tela!", ownerWindow);
      LOGGER.error(e.getMessage(), e);
    }
  }

  /* (non-Javadoc)
   * @see javafx.fxml.Initializable#initialize(java.net.URL, java.util.ResourceBundle)
   */
  @Override
  public void initialize(URL location, ResourceBundle resources) {
    try {
      if (processService.pullList().size() != 0) {
        createChartQntPerMonthAndYear();
        createChartQntLastYear();
        createPieChartSubject();
      } else {
        ExceptionAlert.show("Não há dados para as estatísticas", root.getScene().getWindow());
      }
    } catch (DatabaseException e) {
      LOGGER.error(e.getMessage(), e);
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
    }
  }

  /**
   * Cria um gráfico de barras distribuíndo a criação de objetos que implementam {@code Process}
   * pelos meses e anos.
   */
  private void createChartQntPerMonthAndYear() {
    /* Converte o array em uma lista e adiciona em nossa ObservableList de meses. */
    monthsObsList.addAll(Arrays.asList(Month.getAll()));
    /* Associa os nomes de mês como categorias para o eixo horizontal. */
    categoryAxisMonthYear.setCategories(monthsObsList);

    Map<Integer, ArrayList<Integer>> qntPerMonthData = null;
    try {
      qntPerMonthData = statisticService.quantityProcessPerMonthYear();
    } catch (DatabaseException e) {
      LOGGER.error(e.getMessage(), e);
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
    }

    if (qntPerMonthData != null && !qntPerMonthData.isEmpty()) {
      for (Entry<Integer, ArrayList<Integer>> itemData : qntPerMonthData.entrySet()) {
        XYChart.Series<String, Number> series = new XYChart.Series<>();
        series.setName(itemData.getKey().toString());
        for (int i = 0; i < itemData.getValue().size(); i = i + 2) {
          String month;
          Number quantity;
          month = Month.getName((int) itemData.getValue().get(i));
          quantity = itemData.getValue().get(i + 1);
          series.getData().add(new XYChart.Data<>(month, quantity));
        }
        bcPerMonthYear.getData().add(series);
      }
    }
  }

  /**
   * Cria um gráfico de barras mostrando a contagem de processos para cada um dos 12 últimos meses.
   */
  private void createChartQntLastYear() {

    // Converte o array em uma lista e adiciona em nossa ObservableList de meses.
    lastTwelveMonthsObsList.addAll(this.getMonthList(Calendar.getInstance()));
    // Associa os nomes de mês como categorias para o eixo horizontal.
    categoryAxisLastYear.setCategories(lastTwelveMonthsObsList);

    Map<Integer, ArrayList<Integer>> dados = null;
    try {
      dados = statisticService.quantityProcessFromLastYear();
    } catch (DatabaseException e) {
      LOGGER.error(e.getMessage(), e);
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
    }

    if (dados != null && !dados.isEmpty()) {
      for (Entry<Integer, ArrayList<Integer>> itemData : dados.entrySet()) {
        XYChart.Series<String, Number> series = new XYChart.Series<>();
        series.setName(itemData.getKey().toString());
        for (int i = 0; i < itemData.getValue().size(); i = i + 2) {
          String month;
          Number quantity;
          month = Month.getName((int) itemData.getValue().get(i));
          quantity = itemData.getValue().get(i + 1);
          series.getData().add(new XYChart.Data<>(month, quantity));
        }
        bcLastTwelveMonths.getData().add(series);
      }
    }

  }

  /**
   * Adiquire a lista dos doze últimos meses a partir da data atual.
   * 
   * @param currentDate Data atual
   * @return Lista com os nomes dos últimos 12 meses.
   */
  private List<String> getMonthList(Calendar currentDate) {
    List<String> monthList = new ArrayList<>();

    Deque<String> temporaryMonthDeque = new LinkedList<>();

    // Add the current month value in the stack
    int currentMonthValue = currentDate.get(Calendar.MONTH);
    temporaryMonthDeque.push(Month.getName(currentMonthValue + 1));

    // Add the other 11 months
    for (int i = 0; i < 11; i++) {
      currentDate.add(Calendar.MONTH, -1);
      int monthValue = currentDate.get(Calendar.MONTH);
      temporaryMonthDeque.push(Month.getName(monthValue + 1));
    }

    // Add in a list in the correct order
    for (int i = 0; i < 12; i++) {
      monthList.add(temporaryMonthDeque.pop());
    }

    return monthList;
  }

  /**
   * Método para execução do evento de clique no botão rádio "Situação". Mostra um gráfico em pizza
   * com as contagens dos processos distribuídos por situação.
   */
  @FXML
  private void createPieChartSituation() {
    try {
      pieChart.getData().clear(); // Clean data chart
      Map<Integer, Integer> dados = statisticService.quantityProcessPerSituation();
      this.createPieChart("Situação", dados);
    } catch (DatabaseException e) {
      LOGGER.error(e.getMessage(), e);
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
    }
  }

  /**
   * Método para execução do evento de clique no botão rádio "Orgão". Mostra um gráfico em pizza
   * com as contagens dos processos distribuídos por orgão.
   */
  @FXML
  private void createPieChartOrganization() {
    try {
      pieChart.getData().clear(); // Clean data chart
      Map<Integer, Integer> dados = statisticService.quantityProcessPerOrganization();
      this.createPieChart("Órgão", dados);
    } catch (DatabaseException e) {
      LOGGER.error(e.getMessage(), e);
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
    }
  }

  /**
   * Método para execução do evento de clique no botão rádio "Assunto". Mostra um gráfico em pizza
   * com as contagens dos processos distribuídos por assunto.
   */
  @FXML
  private void createPieChartSubject() {
    try {
      pieChart.getData().clear(); // Clean data chart
      Map<Integer, Integer> data = statisticService.quantityProcessPerSubject();
      this.createPieChart("Assunto", data);
    } catch (DatabaseException e) {
      LOGGER.error(e.getMessage(), e);
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
    }
  }

  /**
   * Método para execução do evento do botão de voltar. Fecha a tela.
   */
  @FXML
  private void closeWindow() {
    Stage janela = (Stage) root.getScene().getWindow();
    if (janela != null)
      janela.close();
  }


  /**
   * Cria um gráfico de pizza a partir da categoria e dados fornecidos.
   * 
   * @param category Rótulo da categoria
   * @param data Dados
   */
  private void createPieChart(String category, Map<Integer, Integer> data) {
    if (data != null && !data.isEmpty()) {
      pieChart.setLabelsVisible(false);
      pieChart.setTitle("Quantidade de Processos por " + category);

      Iterator<Entry<Integer, Integer>> it = data.entrySet().iterator();
      while (it.hasNext()) {
        Map.Entry<Integer, Integer> pair = it.next();

        int categoryId = Integer.parseInt(pair.getKey().toString());
        String categoryName = this.getCategoryNameById(categoryId, category);
        double quantity = Double.parseDouble(pair.getValue().toString());

        Data slice = new PieChart.Data(categoryName, quantity);
        pieChart.getData().add(slice);

        it.remove(); // avoids a ConcurrentModificationException
      }

      pieChart.getData().forEach(this::installTooltip);
    }
  }

  /**
   * Obtem o nome de um elemento da categoria
   * 
   * @param categoryId Id do elemento.
   * @param category Nome da categoria
   * @return Nome do ememento
   */
  private String getCategoryNameById(int categoryId, String category) {
    if (category.equalsIgnoreCase("Situação")) {
      return listService.getSituationDescritionById(categoryId);
    } else if (category.equalsIgnoreCase("Órgão")) {
      return listService.getOrganizationInitialsById(categoryId);
    } else if (category.equalsIgnoreCase("Assunto")) {
      return listService.getSujectShortDescritionById(categoryId);
    } else {
      return null;
    }
  }

  /**
   * Define tooltips para as fatias do gráfico de pizza.
   * @param pcData Dado do gráfico.
   * 
   * {@link http://acodigo.blogspot.com.br/2017/08/piechart-javafx.html}
   */
  public void installTooltip(PieChart.Data pcData) {

    String message = String.format("%s : %s", pcData.getName(), (int) pcData.getPieValue());

    Tooltip tolltip = new Tooltip(message);
    tolltip.setStyle("-fx-background-color: gray; -fx-text-fill: whitesmoke;");

    Tooltip.install(pcData.getNode(), tolltip);
  }

  /**
   * Classe estática interna para obtenção dos nomes abreviados dos meses do ano. 
   * 
   * @author hugo
   */
  private static class Month {
    private static String[] names =
      {"Jan", "Fev", "Mar", "Abr", "Mai", "Jun", "Jul", "Ago", "Set", "Out", "Nov", "Dez"};

    private Month() {}

    private static String getName(int order) {
      if (order > 0 && order <= 12) {
        return names[order - 1];
      } else {
        return null;
      }
    }

    private static String[] getAll() {
      return names;
    }
  }
}
