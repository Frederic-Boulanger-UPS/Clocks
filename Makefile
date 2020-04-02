# Change next definition to the path to the isabelle binary you want to use
ISABELLE=/usr/local/bin/isabelle2019

# Name of your session
SESSIONNAME=LinguaFrancaClocks

# Description
DESCRIPTION="A clock calculus for Lingua Franca"

# List of theories in the session
THEORIES="LinguaFrancaClocks LinguaFrancaLogicalTime LinguaFrancaTests"

# Document files (.tex, .bib and so on)
DOCUMENTS="root.tex"

# Your name
AUTHORNAME="Frédéric Boulanger"

# Your email address
EMAIL=frederic.boulanger@lri.fr

browser_info:
	$(ISABELLE) build -c -d . -o browser_info -v $(SESSIONNAME)
	mv "`$(ISABELLE) getenv -b ISABELLE_BROWSER_INFO`/Unsorted/$(SESSIONNAME)" .
	rm -fr docs
	mv $(SESSIONNAME) docs
	sed -i -e 's/Session/Library/g' docs/index.html
	sed -i -e 's!</body>!<p><a href="mailto:$(EMAIL)">$(EMAIL)</href></p></body>!' docs/index.html
	sed -i -e 's!../../HOL/HOL/!http://isabelle.in.tum.de/website-Isabelle2019/dist/library/HOL/HOL/!' docs/$(SESSIONNAME).html

pdf_document:
	$(ISABELLE) build -D .


reboot:
	rm -rf ROOT ROOT-e document output docs
	$(ISABELLE) mkroot -n $(SESSIONNAME) -A $(AUTHORNAME) .
	rm ROOT
	echo "session \"$(SESSIONNAME)\" = HOL +" >> ROOT
	echo "	description {* $(DESCRIPTION) *}" >> ROOT
	echo "	options [" >> ROOT
	echo "		document = pdf," >> ROOT
	echo "		document_output = \"output\"," >> ROOT
	echo "		document_variants=\"document:outline=/proof\"" >> ROOT
# uncomment the next line if you have sorry proofs or other failures in your theories
#	echo "		,quick_and_dirty = true" >> ROOT
	echo "	]" >> ROOT
	echo "theories" >> ROOT
	@for th in $(THEORIES) ; \
	do \
		echo "	$${th}" >> ROOT ; \
	done
	echo "document_files" >> ROOT
	@for doc in $(DOCUMENTS) ; \
	do \
		echo "	\"$${doc}\"" >> ROOT ; \
	done

