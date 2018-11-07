CREATE TABLE interessados (
	id BIGINT NOT NULL AUTO_INCREMENT,
        nome VARCHAR(255) NOT NULL,
        cpf VARCHAR(11) NOT NULL UNIQUE,
        contato VARCHAR(20),
        PRIMARY KEY (id),
	UNIQUE KEY (cpf,nome)
	
);
