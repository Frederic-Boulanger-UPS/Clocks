ISABELLE=/usr/local/bin/isabelle2019

browser_info:
	$(ISABELLE) build -c -d . -o browser_info -v Clocks
	mv "`$(ISABELLE) getenv -b ISABELLE_BROWSER_INFO`/Unsorted/Clocks" .
	rm -fr docs
	mv Clocks docs
	sed -i -e 's/Session/Library/g' docs/index.html
#	sed -i -e 's!<h2>Theories</h2>!<h2><a href="session_graph.pdf">Index</a></h2>!g' docs/index.html
	sed -i -e 's!</body>!<p><a href="mailto:frederic.boulanger@lri.fr">frederic.boulanger@lri.fr</href></p></body>!' docs/index.html
	sed -i -e 's!../../HOL/HOL/!http://isabelle.in.tum.de/website-Isabelle2019/dist/library/HOL/HOL/!' docs/Clocks.html

pdf_document:
	$(ISABELLE) build -D .


reboot:
	rm -rf ROOT ROOT-e document output docs
	$(ISABELLE) mkroot -n Clocks -A "Frédéric Boulanger" .
	rm ROOT
	echo "session \"Clocks\" = HOL +" >> ROOT
#	echo "	description {* Clock calculus for Lingua Franca *}" >> ROOT
	echo "	options [" >> ROOT
	echo "		document = pdf," >> ROOT
	echo "		document_output = \"output\"," >> ROOT
	echo "		document_variants=\"document:outline=/proof\"" >> ROOT
	echo "	]" >> ROOT
	echo "theories" >> ROOT
	echo "	Clocks" >> ROOT
	echo "document_files" >> ROOT
	echo "		\"root.tex\"" >> ROOT
