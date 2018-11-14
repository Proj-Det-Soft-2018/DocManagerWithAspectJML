<?xml version="1.0" encoding="UTF-8"?>

<xsl:stylesheet version="1.0"
	xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:fo="http://www.w3.org/1999/XSL/Format">

	<xsl:template match="/process">
		<fo:root xmlns:fo="http://www.w3.org/1999/XSL/Format"
			hyphenate="false" role="html" text-align="justify" writing-mode="lr-tb"
			xml:lang="pt-br">
			<fo:layout-master-set>
				<fo:simple-page-master master-name="all-pages"
					page-height="1123pt" page-width="794pt">
					<fo:region-body column-count="1" column-gap="12pt"
						margin-bottom="3cm" margin-left="2cm" margin-right="2cm"
						margin-top="6cm" />
					<fo:region-before display-align="before" extent="6cm"
						region-name="page-header" />
					<fo:region-after display-align="after" extent="3cm"
						region-name="page-footer" />
					<fo:region-start extent="2cm" />
					<fo:region-end extent="2cm" />
				</fo:simple-page-master>
			</fo:layout-master-set>

			<fo:page-sequence master-reference="all-pages">
				<fo:title>Declaração</fo:title>
				<fo:static-content flow-name="page-header">
					<fo:block font-size="small" space-before="2cm"
						space-before.conditionality="retain" text-align="center"
						display-align="center">
						<fo:table border="1px solid black" border-collapse="separate"
							border-spacing="2px" padding="10px 10px" table-layout="fixed"
							width="100%">
							<fo:table-body>
								<fo:table-row>
									<fo:table-cell>
										<fo:block>
											<fo:block>
												<fo:external-graphic src="fo_templates/img/ufrn.png"
													content-width="90pt" />
											</fo:block>
										</fo:block>
									</fo:table-cell>
									<fo:table-cell text-align="center" width="35em">
										<fo:block>
											UNIVERSIDADE FEDERAL DO RIO GRANDE DO NORTE - UFRN&#8232;
											Subsistema Integrado de Atenção à Saúde do Servidor -
											SIASS&#8232;
											&#8232;
											<fo:inline role="span"> Emitido em <xsl:value-of select="current-time"/>
											</fo:inline>
										</fo:block>
									</fo:table-cell>
									<fo:table-cell>
										<fo:block>
											<fo:block>
												<fo:external-graphic src="fo_templates/img/siass.png"
													content-width="90pt" />
											</fo:block>
										</fo:block>
									</fo:table-cell>
								</fo:table-row>
							</fo:table-body>
						</fo:table>
					</fo:block>
				</fo:static-content>
				<fo:static-content flow-name="page-footer">
					<fo:block space-after="2cm" space-after.conditionality="retain">
						<fo:table border="1px solid black" border-collapse="separate"
							border-spacing="2px" padding="10px 10px" table-layout="fixed"
							width="100%">
							<fo:table-body>
								<fo:table-row>
									<fo:table-cell text-align="center">
										<fo:block>
											DocManager - 2018 - Projeto Detalhado de Software -
											https://github.com/Proj-Det-Soft-2018/DocManager
										</fo:block>
									</fo:table-cell>
								</fo:table-row>
							</fo:table-body>
						</fo:table>
					</fo:block>
				</fo:static-content>
				<fo:flow flow-name="xsl-region-body">
					<fo:block font-size="1.5em" font-weight="bold"
						keep-together.within-column="always" keep-with-next.within-column="always"
						role="h2" space-after="1.66em" space-before="0.83em" text-align="center">
						DECLARAÇÃO DE STATUS DO PROCESSO NA UNIDADE
					</fo:block>

					<fo:table margin="0 0.2cm" table-layout="fixed" width="100%-0.4cm">
						<fo:table-body>
							<fo:table-row>
								<fo:table-cell width="4.5cm">
									<fo:block>
										<fo:inline font-weight="bold">
											<xsl:value-of select="type" />
											Número:
										</fo:inline>
									</fo:block>
								</fo:table-cell>
								<fo:table-cell>
									<fo:block>
										<xsl:value-of select="number" />
									</fo:block>
								</fo:table-cell>
							</fo:table-row>
						</fo:table-body>
					</fo:table>
					<fo:block>&#8232;
					</fo:block>
					<fo:table margin="0 0.2cm" table-layout="fixed" width="100%-0.4cm">
						<fo:table-body>
							<fo:table-row>
								<fo:table-cell width="90pt">
									<fo:block />
								</fo:table-cell>
								<fo:table-cell>
									<fo:block />
								</fo:table-cell>
							</fo:table-row>
							<fo:table-row role="tr">
								<fo:table-cell number-columns-spanned="2">
									<fo:block>
										<fo:inline font-weight="bold" role="strong">INTERESSADO
										</fo:inline>
									</fo:block>
								</fo:table-cell>
							</fo:table-row>
							<fo:table-row>
								<fo:table-cell>
									<fo:block>
										<fo:inline font-weight="bold">Nome:</fo:inline>
									</fo:block>
								</fo:table-cell>
								<fo:table-cell>
									<fo:block><xsl:value-of select="interested/name"/></fo:block>
								</fo:table-cell>
							</fo:table-row>
							<fo:table-row>
								<fo:table-cell>
									<fo:block>
										<fo:inline font-weight="bold">CPF:</fo:inline>
									</fo:block>
								</fo:table-cell>
								<fo:table-cell>
									<fo:block><xsl:value-of select="interested/cpf"/>
									</fo:block>
								</fo:table-cell>
							</fo:table-row>
						</fo:table-body>
					</fo:table>
	       			<fo:block>&#8232;
					</fo:block>
			        <fo:table margin="0 0.2cm" table-layout="fixed" width="100%-0.4cm">
			          <fo:table-body>
			            <fo:table-row>
			              <fo:table-cell width="135pt">
			                <fo:block>
			                  <fo:inline font-weight="bold">Unidade de Origem:</fo:inline>
			                </fo:block>
			              </fo:table-cell>
			              <fo:table-cell>
			                <fo:block><xsl:value-of select="origin-entity"/></fo:block>
			              </fo:table-cell>
			            </fo:table-row>
			            <fo:table-row>
			              <fo:table-cell>
			                <fo:block>
			                  <fo:inline font-weight="bold">Assunto:</fo:inline>
			                </fo:block>
			              </fo:table-cell>
			              <fo:table-cell>
			                <fo:block><xsl:value-of select="subject"/></fo:block>
			              </fo:table-cell>
			            </fo:table-row>
			            <fo:table-row>
			              <fo:table-cell>
			                <fo:block>
			                  <fo:inline font-weight="bold">Situação:</fo:inline>
			                </fo:block>
			              </fo:table-cell>
			              <fo:table-cell>
			                <fo:block><xsl:value-of select="situation"/></fo:block>
			              </fo:table-cell>
			            </fo:table-row>
			            <fo:table-row>
			              <fo:table-cell>
			                <fo:block>
			                  <fo:inline font-weight="bold">Observações:</fo:inline>
			                </fo:block>
			              </fo:table-cell>
			              <fo:table-cell text-align="justify">
			                <fo:block><xsl:value-of select="observation"/></fo:block>
			              </fo:table-cell>
			            </fo:table-row>
			          </fo:table-body>
			        </fo:table>
			       <fo:block>&#8232;
				   </fo:block>
		  		</fo:flow>
			</fo:page-sequence>
		</fo:root>
	</xsl:template>
</xsl:stylesheet>