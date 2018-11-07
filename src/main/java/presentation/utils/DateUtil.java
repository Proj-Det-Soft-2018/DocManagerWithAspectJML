package presentation.utils;

import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;


/**
 * Classe de utilidades para processamento de informações sobre datas.
 * 
 * @author hugo
 */
public class DateUtil {

  /**
   * Padrão de escrita de data utilizado para as conversões.
   */
  private static final String DATE_PATTERN = "dd/MM/yy";
  /**
   * Objeto {@code DateTimeFormatter} utilizado para as conversões String/LocalDateTime.
   */
  private static final DateTimeFormatter DATE_FORMATER = DateTimeFormatter.ofPattern(DATE_PATTERN);


  /**
   * Método que recebe um objeto {@code LocalDateTime} e retorna uma string formatada no padrão
   * "{@code dd/MM/yy}" para a data armazenada.
   * 
   * @param date Objeto {@code LocalDateTime} com a data que se quer converter.
   * @return {@code String} formatada ou {@code null} caso entrada também o seja.
   */
  public static String format(LocalDateTime date) {
    if (date != null) {
      return DATE_FORMATER.format(date);
    }
    return null;
  }

  /**
   * Método de conversão de uma {@code String} que obedeça o padrão "{@code dd/MM/yy}" em um objeto
   * {@code LocalDateTime} com a data desejada.
   * 
   * @param dateString {@code String} com a data desejada.
   * @return {@code LocalDateTime} com a data ou {@code null} para as entradas mau formatadas.
   */
  public static LocalDateTime parse(String dateString) {
    try {
      return LocalDateTime.parse(dateString, DATE_FORMATER);
    } catch (DateTimeParseException e) {
      return null;
    }
  }

  /**
   * Construtor privado para impedir a instanciação de objetos do tipo {@code DateUtil}.
   */
  private DateUtil() {}
}
