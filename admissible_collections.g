#
#    Code for the paper arXiv:2005.02658
#
#"A geometric approach to Quillen's conjecture" 
#                   by
#    Antonio Díaz Ramos and Nadia Mazza
#

#
#The code below is a GAP script to find "addmissible collections" in a group G at the prime p.
#The term "admissible collection" is defined in Definition 3.6 of the paper above.
#Explicit "admissible collections" found by this script are described and employed in the proof ot Theorem 4.7 of the paper above.
#

#example group and prime
G:=SL(6,2);
p:=3;

#find p-Sylow subgroup and p-rank
S:=SylowSubgroup(G,p);
r:=RankPGroup(S);

#find elementary abelian p-subgroups of S of rank r up to G-conjugacy
CCS:=ConjugacyClassesSubgroups(S);
temp:=List(Filtered(List(CCS,x->x[1]),x->RankPGroup(x)=r),x->ConjugacyClassSubgroups(G,x));
EASrankr:=List(Unique(temp),x->x[1]);

#create empty lists for later
centralizer:=EmptyPlist(r);
normalizer:=EmptyPlist(r);
diff:=EmptyPlist(r);

#create counter for admissible collections
num_admissible_collections:=0;

#for each each elementary abelian p-subgroup of rank r, try to find admissible collection
for i in [1..Size(EASrankr)] do

	EA:=EASrankr[i]; # target elementary abelian p-subgroup of rank r of G
	LCCEA:=Filtered(List(ConjugacyClassesSubgroups(EA),x->x[1]),x->RankPGroup(x)=1); # rank 1 subgroups of EA
	LEA:=List(LCCEA,x->List(x)[2]); # generators of the rank 1 subgroups

	#form the r-folded cartesian product LEAtor of EA as a list
	temp:=[];
	for j in [1..r] do
		temp[j]:=LEA;
	od;
	LEAtor:=Cartesian(temp);
	
	#go through LEAtor looking for admissible collection
	for j in [1..Size(LEAtor)] do
		rtuplefromEA:=LEAtor[j];		
		
		if RankPGroup(Subgroup(G,rtuplefromEA))=r then		
			#rank is correct, check now for centralizers, normalizers and commuting
			candidates:=true;
			for k in [1..r] do	
				copyofrtuple:=ShallowCopy(rtuplefromEA);	
				Remove(copyofrtuple,k);
				EAk:=Subgroup(EA,copyofrtuple);
				centralizer[k]:=List(Centralizer(G,EAk));			
				rank1ek:=Subgroup(G,[rtuplefromEA[k]]);
				diff[k]:=Filtered(centralizer[k],x->not (x*rtuplefromEA[k]*Inverse(x) in rank1ek));
				if IsEmpty(diff[k]) then
					candidates:=false;
					break;
 			fi;
			od;
			if not candidates then # some centralizer \ normalizer was empty, so consider next elementary abelian p-subgroup of rank r
				continue;
			fi;
			#form cartesian product with potential candidates to elements c_j
			temp:=[];
			for k in [1..r] do
				temp[k]:=List(diff[k]);
			od;
			candidatestoc:=Cartesian(temp);	

			#if candidatestoc is not empty, check for commutativity of elements c_j
			for k in [1..Size(candidatestoc)] do
				rtupleofcc:=candidatestoc[k];
				commutes:=true;				
				for l in [1..r] do
					x:=rtupleofcc[l];
					for m in [l+1..r] do
						y:=rtupleofcc[m];
						commutes:=commutes and (x*y=y*x);					
					od;
				od;
				if commutes then
					num_admissible_collections:=num_admissible_collections+1;
					Print("Group ",G," has ",num_admissible_collections," admissible collections.\n");					
				fi;
			od;
		fi;
	od;
od;
Print("Group ",G," has ",num_admissible_collections," admissible collections.\n");