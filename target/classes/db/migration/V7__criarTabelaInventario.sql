DROP TABLE if exists inventario;
CREATE TABLE inventario (
	id BIGINT NOT NULL AUTO_INCREMENT,
	
    numero VARCHAR(100) NOT NULL,
    inventariante_id BIGINT NOT NULL,
	assunto INT NOT NULL,
	situacao INT NOT NULL,
	vara INT NOT NULL,
	advogado VARCHAR(255) NOT NULL,
	inventariado VARCHAR(255) NOT NULL,
    observacao VARCHAR(255),
	data_entrada DATE,
    
    PRIMARY KEY (id),
	INDEX (inventariante_id),
	FOREIGN KEY (inventariante_id)
        	REFERENCES inventariante(id)
) ENGINE = InnoDB;