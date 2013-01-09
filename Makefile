all: Basics.vo Poly.vo Gen.vo Prop.vo Logic.vo Rel.vo SfLib.vo Imp.vo \
	Equiv.vo Hoare.vo HoareAsLogic.vo  Smallstep.vo Types.vo


%.vo: %.v
	coqc $<
