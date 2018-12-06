# DocManager
O DocManager é um sistema desenvolvido como item avaliativo da disciplica de Projeto Detalhado de Software do Bacharelado em Tecnologia da Informação (BTI) do [Instituto Metrópole Digital (IMD)](https://portal.imd.ufrn.br/) da Universidade Federal do Rio Grande do Norte (UFRN).

O objetivo deste sistema é gerenciar os processos em uma unidade de assistência à saúde do servidor, com todas as atribuições de um CRUD (Criar, Ler, Alterar e Deletar). Vindo para substituir o uso de planilhas e tendo a vantagem de padronizar o formato dos processos, garantir segurança aos dados e melhorar o armazenamento.


## Começando
As seguintes instruções vão orientar sobre o que é necessário para ter este projeto funcionando em sua versão de desenvolvimento.

### Guia de Estilo
As regras de estilo utilizadas neste projeto foram as encontradas em [Google Java Style Guide](https://google.github.io/styleguide/javaguide.html).

### Pré-requisitos

* **Oracle Java 8 SDK:** disponível na página de [download](http://www.oracle.com/technetwork/pt/java/javase/downloads/index.html) oficial da Oracle.
No Linux Ubuntu sua instalação pode ser obtida pelos comandos:
	```
	sudo add-apt-repository ppa:webupd8team/java
	sudo apt-get update
	sudo apt-get install oracle-java8-installer
	```
	E para configuração automática das variáveis de ambiente:
	```
	sudo apt-get install oracle-java8-set-default
	```
* **MySQL:** o projeto está configurado para este banco, sua instalação do Linux Ubuntu pode ser adquirida utilizando os repositórios oficiais utilizando o comando:
	```
	sudo apt-get install mysql-server
	```
* **Eclipse:** este projeto está sendo desenvolvido utilizando esta IDE (em sua versão Oxigen) que está disponível para [download](https://www.eclipse.org/downloads/)  em seu site oficial.

### Ferramentas Indicadas

* **Eclipse Checkstyle Plug-in 8.10.0**: Pluggin para checagem estática de estilo.
	Para sua instalação, na ferramenta Eclipse: 
1. Na aba **Help** clique em **Eclipse Marketplace...**
2. Busque por "checkstyle" e selecione o plug-in para a instalação.

* **e(fx)clipse:** pluggin do eclipse com ferramentas para desenvolvimento com JavaFX.
	Para sua instalação, na ferramenta Eclipse: 
1. Na aba **Help** clique em **Install New Software...**
2. No campo **Work with** selecione ***--All Available Sites --***
3. Na lista que será mostrada, dentro de ***General Purpose Tools*** escolha **e(fx)clipse-IDE** e clique em **Next>**
4. Clique em **Nest>** para confirmar a escolha
5. Aceite o termo de licença e clique em **Finish**.
	
* **SceneBuilder 2.0:** ferramenta para edição de arquivos .fxml utilizados pelo JavaFX.
	Pode ser adquirido na página oficinal de [download](www.oracle.com/technetwork/java/javafxscenebuilder-1x-archive-2199384.html) da Oracle.

### Instalação
Para utilização do DocManager é necessaria a criação do banco "docmanager" e as tabelas neste banco. Para tanto, no Ubuntu:
1. abra o Terminal e execute o comando para abrir o **MySQL**:
	```
	mysql -u root -p
	```
2. Digite a senha para o usuário *root*, solicitada e na tela de comando do MySQL execute os seguintes comandos:

	```
	CREATE DATABASE docmanager;
	```
	```
	USE docmanager;
	```
	```
	CREATE TABLE interessados (
		id BIGINT NOT NULL AUTO_INCREMENT,
		nome VARCHAR(255) NOT NULL,
		cpf VARCHAR(11) NOT NULL UNIQUE,
		contato VARCHAR(20),
		PRIMARY KEY (id),
		UNIQUE KEY (cpf,nome)
	) ENGINE = InnoDB;
	```
	```
	CREATE TABLE processos (
		id BIGINT NOT NULL AUTO_INCREMENT,
		eh_oficio BOOLEAN NOT NULL,
		numero VARCHAR(100) NOT NULL,
		interessado_id BIGINT NOT NULL,
		assunto INT NOT NULL,
		situacao INT NOT NULL,
		orgao_origem INT NOT NULL,
		observacao VARCHAR(255),
		data_entrada DATE,
		data_saida DATE,
		orgao_saida INT,
		PRIMARY KEY (id),
		INDEX (interessado_id),
		FOREIGN KEY (interessado_id)
		REFERENCES interessados(id)
	) ENGINE = InnoDB;
	```
3. Feche o MySQL.
	```
	quit;
	```

Agora na ferramenta Eclipse:

1. Vá em **File** > **Open Projects from File System...**
2. Na próxima tela escolha a pasta raiz contendo os arquivos obtidos neste repositório e clique em **Finish**
3. Se sua **JRE System Library** estiver como [J2ME-1.5] (Padrão) no *Package Explorer*, clique com o botão direito sobre ele e escolha **Properties**. Na tela aberta escolha *JavaSE-1.8* como **Execution environment**
4. Clique com o botão direito no projeto, vá em **Build Path** >> **Configure Build Path**
5. Na aba **Source** clique no botão **Add Folder** e selecione a pasta **src/main/resources**
6. Clique em **Apply and Close**
7. Agora vá em **Run** >> **Run Configurations...**
8.  Crie uma nova **Java Aplication**
9. Na aba **Main**, selecione o *Workspace* do *DocManager* como *Base Directory* e em *Main Class:* **Main**
10. Na aba **Classpath**, clique em **User Entries** e aperte o botão **Advanced...**
11. Selecione **Add Folders**, clique em **Ok** e na proxima tela escolha a pasta de recursos da aplicação escolhida.
12. Na aba **Environment** e crie a variável *DATABASE_PASSWORD* com sua senha de ***root*** do banco como *Value*.

## Este projeto utiliza

* [Apache Shiro](https://shiro.apache.org/) - Framework de Segurança
* [Apache Xalan](https://xalan.apache.org/) - Transformação de XML para XSL:FO
* [Apache FOP](https://xmlgraphics.apache.org/fop/) - Geração de documentos PDF a partir de XSL:FO

## Autores

* **Allan Gonçalves** - *desenvolvedor* - [allangoncalves](https://github.com/allangoncalves)
* **Clarissa Soares** - *idealizadora/desenvolvedora* - [clahzita](https://github.com/clahzita)
* **Hugo Oliveira** - *desenvolvedor* - [HugoTHO](https://github.com/HugoTHO)
