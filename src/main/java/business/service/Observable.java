package business.service;

import java.util.ArrayList;
import java.util.List;

/**
 * Classe que implementa o padrão de projeto "Observer", em que é responsavel por manter classes
 * atualizadas através de notificações lançadas aos observadores quando ocorrer alterações no objeto
 * observável.
 *
 */
public abstract class Observable {

  List<Observer> observers = new ArrayList<>();

  /**
   * Anexa um observador a classe.
   * 
   * @param obs Observador que será notificado quando houver alterações no observável.
   */
  public void attach(Observer obs) {
    this.observers.add(obs);
  }

  /**
   * Desanexa um observador da classe.
   * 
   * @param obs Observador que será desanexado da classe.
   */
  public void dettach(Observer obs) {
    this.observers.remove(obs);
  }

  /**
   * Notifica todos os observadores sobre uma alteração ocorrida.
   */
  public void notifyObservers() {
    this.observers.forEach(Observer::update);
  }
}
