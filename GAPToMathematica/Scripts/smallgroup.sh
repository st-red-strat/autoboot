#!/bin/sh

if [ "$#" -ne "2" -a "$#" -ne "3" ]; then
   echo "Usage: smallgroup.sh <order> <id> [:unitary]"
   exit 1
fi;

gap -b -q -x 800 << EOI
g := SmallGroup($1, $2);
hom := EpimorphismFromFreeGroup(g);
hom2 := function(x)
return ExtRepOfObj(PreImagesRepresentative(hom, x));
end;
ct := Irr(g);
gen := GeneratorsOfGroup(g);
irrs := List(ct, x -> IrreducibleRepresentationsDixon(g, x$3));
calcG := function()
local x, irr;
Print("(id)=", IdGroup(g));
Print("(cgsize)=", List(ConjugacyClasses(g), x -> Size(x)));
Print("(chartab)=");
for x in ct do Print(List(x)); od;
Print("(gen)=", List(GeneratorsOfGroup(g), hom2));
Print("(cggen)=", List(ConjugacyClasses(g), x -> hom2(Representative(x))));
Print("(irrep)=");
for irr in irrs do Print(List(gen, y -> Image(irr, y))); od;
Print("(elements)=", List(Elements(g), hom2));
return;
end;
output := OutputTextFile("out.txt", false);
SetPrintFormattingStatus(output, false);
OutputLogTo(output);
calcG();
quit;
EOI
