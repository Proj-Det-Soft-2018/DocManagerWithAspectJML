DROP TABLE if exists inventariante;
CREATE TABLE inventariante (
	id BIGINT NOT NULL AUTO_INCREMENT,
	nome VARCHAR(255) NOT NULL,
	idade int NOT NULL,
	cpf VARCHAR(11) NOT NULL UNIQUE,
	contato VARCHAR(20),
	email VARCHAR(255),
	PRIMARY KEY (id),
	UNIQUE KEY (cpf,nome)
)ENGINE = InnoDB;
