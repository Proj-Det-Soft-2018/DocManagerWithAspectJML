CREATE TABLE processos_compra (
	id BIGINT NOT NULL AUTO_INCREMENT,
	numero VARCHAR(100) NOT NULL,
	descricao VARCHAR(255) NOT NULL,
  interessado_id BIGINT NOT NULL,
	tipo_material INT NOT NULL,
	situacao INT NOT NULL,
	unidade_origem INT NOT NULL,
  observacao VARCHAR(255),
	data_entrada DATE,
	
  PRIMARY KEY (id),
	INDEX (interessado_id),
	FOREIGN KEY (interessado_id)
        	REFERENCES interessados_compra(id)
) ENGINE = InnoDB;