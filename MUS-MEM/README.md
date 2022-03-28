# MUS-MEM

This is a protype algorithm of computing union of justifications using membership-approach.   

#step 1
Put your own ontologies on dictionary "Ontologies". For example, assume "test.owl" is in dictionary "Ontologies".

Then we initializing the algorthm by 

`python main.py test.owl`
>Here, we execute "condor-reasoner/bin/condor" do the classification and save the saturation progress in 'condor-reasoner/classificaion-result/test.owl.txt'.
>Make sure "condor-reasoner/bin/condor" is executable on your computer! For more details, see [condor](https://github.com/ykazakov/condor-reasoner).

#step2
Put all the subsumptions to compute in a file. For example: "queries" with each line of the form:

`SubClassOf(<http://purl.obolibrary.org/obo/FAO_0001009> <http://purl.obolibrary.org/obo/FAO_0001001>)\n`

Then you can compute the union of their justifications by:

`python main.py test.owl queries`
>Here, we use the SAT-tool "cmmus". Make sure it is executable on your computer! For more details, see [cmmus](http://sat.inesc-id.pt/~mikolas/sw/cmmus/).
