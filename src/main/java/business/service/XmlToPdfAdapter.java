package business.service;

/**
 * Interface do adaptador que tranforma as informações do objeto processo de pdf para o documento
 * formatado em Pdf a partir de um template fornecido pela aplicação cliente.
 * 
 * @author hugo
 */
public interface XmlToPdfAdapter {

  /**
   * Método que tem que ser implementado para a utilização da transformação de xml para Pdf pelo 
   * framework
   * 
   * @param xml Xml contendo as informações desejadas
   * @return Binário do documento Pdf.
   */
  byte[] transform(String xml);
}
