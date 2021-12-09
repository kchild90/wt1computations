#ifndef TWISTMINIMAL_H_INCLUDED
#define TWISTMINIMAL_H_INCLUDED

GEN getAltCharStats(long N);
GEN getAllCharStats(long N);

long wt1newformdimension(long N, GEN stats, GEN wt1data);

GEN updateDatabaseForLevel(GEN database, long N, long maxM);

long wt1newformDimFromExp(GEN N, GEN chiexp, GEN database);

char getLMFDBlabel(GEN N, GEN chiExp);

GEN generateLMFDBorder(GEN group, GEN chars);

GEN lmfdbToLog(long N, long lab);

GEN getMinimalEquiv(long N, GEN stats);

void getFormDetails(GEN N, GEN chiexp, GEN database);

GEN bestRep(GEN group, GEN convec);

long verifywt2(long N);

void specifTrace(long N, long n);

long getDihedralDim(long N, GEN stats, GEN database);

long canHaveExotic(long N, GEN stats);

void displayForms(GEN N, GEN chiexp, GEN database, long numcoefs);

GEN myLowStackInverse(GEN M);


#endif // TWISTMINIMAL_H_INCLUDED
