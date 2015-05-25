.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile.source
	coq_makefile -f Makefile.source -o Makefile.coq

gen-html:
	$(MAKE) -f Makefile.coq html COQDOCFLAGS="-interpolate -utf8 -g"

gen-tex:
	$(MAKE) -f Makefile.coq latex

clean:
	rm -f */*.vo */*.v.d */*.glob */*~ */.#* Makefile.coq
	rm -f */*/*.vo */*/*.v.d */*/*.glob

coqide:
	coqide -R . Brenner
