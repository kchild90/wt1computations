#include <stdio.h>
#include<omp.h>
#include <stdlib.h>
#include <pari/pari.h>
#include <pari/paripriv.h>
#include <time.h>
#include <string.h>
#include "twistminimal.h"
#include <sys/file.h>
#include <errno.h>
#include <limits.h>


int
main( int argc, char *argv[] )
{

    if(argc==2){
        pari_init(10000000,1);
        paristack_setsize(1999999999,  49999999999);
        long N = atoi(argv[1]);
        char filename[30];
        sprintf(filename, "wt1correctdims/%ld.txt", N);
        FILE *out_file = fopen(filename, "w");
        GEN group = znstar0(stoi(N),1);
        GEN chars = getAllCharStats(N);
            for(int i=1; i<lg(chars); i++)
            {
                pari_sp lmed = avma;
                int parisComputedDimension = itos(mfdim(mkvec3(stoi(N),gen_1,mkvec2(group,gel(chars,i))), 0));
                pari_fprintf(out_file, "%Ps\n", mkvec3(stoi(N),gel(chars,i),stoi(parisComputedDimension)));
                set_avma(lmed);
            }
        pari_printf("Generated level %ld\n",N);
        fclose(out_file);
        return 0;
    }
    if(argc==4){
    long RAMallowed = atol(argv[3]);
    pari_init(10000000,1);
    paristack_setsize(250000000, RAMallowed);
    pari_printf("ramallowed is %ld\n", RAMallowed);
    int maxM = atoi(argv[1]);
    long threadnum = atoi(argv[2]);
    if(threadnum<1){
        sleep(5-threadnum*8);
        return 0;
    }
    FILE *fptr = fopen("wt1_conrey_dihedral_dims.txt", "r"); // read in
    GEN dihedralDims = zerovec(20000);
    char line[100];
    char sub[20];
    int position = 0;
    while(fgets(line, 100, fptr))
    {
            int c = 0;
            while (line[c]!='.')
            {
                sub[c] = line[c];
                c++;
            }
            sub[c] = '\0';
            int lev = atoi(sub);
            if(lev>10000) break;
            c +=3;
            position = c;
            while (line[c]!=':')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            GEN conreyLog = gp_read_str(sub);
            position = ++c;
            while (line[c]!=':')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            int dihedralDimension = atoi(sub);
             position = ++c;
            while (line[c]!='\n')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            GEN Dlcm = gp_read_str(sub);
            if (gequal0(gel(dihedralDims,lev))){
                gel(dihedralDims, lev) = mkvec(mkvec3(conreyLog, stoi(dihedralDimension), Dlcm));
            } else {
                gel(dihedralDims,lev) = vec_append(gel(dihedralDims,lev), mkvec3(conreyLog, stoi(dihedralDimension), Dlcm));
            }
        }
        GEN database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
        database = updateDatabaseForLevel(database, threadnum, maxM, 0);
        pari_printf("Computed level %ld\n", threadnum);
        return 0;
    }
    if(argc==3){
        pari_init(10000000,1);
    paristack_setsize(250000000, 20000000000);
    int numToProcess = atoi(argv[1]);
    FILE *fptr = fopen("wt1_conrey_dihedral_dims.txt", "r"); // read in
    GEN dihedralDims = zerovec(20000);
    char line[100];
    char sub[20];
    int position = 0;
    while(fgets(line, 100, fptr))
    {
            int c = 0;
            while (line[c]!='.')
            {
                sub[c] = line[c];
                c++;
            }
            sub[c] = '\0';
            int lev = atoi(sub);
            if(lev>10000) break;
            c +=3;
            position = c;
            while (line[c]!=':')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            GEN conreyLog = gp_read_str(sub);
            position = ++c;
            while (line[c]!=':')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            int dihedralDimension = atoi(sub);
             position = ++c;
            while (line[c]!='\n')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            GEN Dlcm = gp_read_str(sub);
            if (gequal0(gel(dihedralDims,lev))){
                gel(dihedralDims, lev) = mkvec(mkvec3(conreyLog, stoi(dihedralDimension), Dlcm));
            } else {
                gel(dihedralDims,lev) = vec_append(gel(dihedralDims,lev), mkvec3(conreyLog, stoi(dihedralDimension), Dlcm));
            }
        }
                GEN something = generateFourierCoefficients(numToProcess, dihedralDims);
            char filename[30];
            sprintf(filename, "wt1coefs/%d.txt", numToProcess);
            FILE *coefs_out = fopen(filename, "w");
            for(int i = 1; i<lg(something); i++){
                pari_fprintf(coefs_out, "%Ps\n", gel(something,i));
            }
            fclose(coefs_out);

        pari_printf("Processed level %ld\n", numToProcess);
        return 0;
    }

    pari_init(1000000,1);
    paristack_setsize(250000000, 15000000000);


    FILE *fptr = fopen("wt1_conrey_dihedral_dims.txt", "r"); // read in
    GEN dihedralDims = cgetg(1,t_VEC);

    if (fptr != NULL)
    {
        dihedralDims = zerovec(20000);
    char line[100];
    char sub[20];
    int position = 0;
    while(fgets(line, 100, fptr))
    {
            int c = 0;
            while (line[c]!='.')
            {
                sub[c] = line[c];
                c++;
            }
            sub[c] = '\0';
            int lev = atoi(sub);
            if(lev>10000) break;
            c +=3;
            position = c;
            while (line[c]!=':')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            GEN conreyLog = gp_read_str(sub);
            position = ++c;
            while (line[c]!=':')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            int dihedralDimension = atoi(sub);
             position = ++c;
            while (line[c]!='\n')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            GEN Dlcm = gp_read_str(sub);
            if (gequal0(gel(dihedralDims,lev))){
                gel(dihedralDims, lev) = mkvec(mkvec3(conreyLog, stoi(dihedralDimension), Dlcm));
            } else {
                gel(dihedralDims,lev) = vec_append(gel(dihedralDims,lev), mkvec3(conreyLog, stoi(dihedralDimension), Dlcm));
            }
        }
        pari_printf("Successfully loaded dihedral dimension data up to level %ld.\n", lg(dihedralDims)-1);
    } else {
        pari_printf("Unable to load dihedral dimension data.\n");
    }
    printf("Please select a mode.\nEnter 1 for weight-1 dimension computations.\nEnter 2 to validate against PARI up to a given level.\nEnter 3 to compare computation time with PARI.\nEnter 4 to time the computation up to a given level.\n");
    int mode = itos(gp_read_stream(stdin));
    if(mode==1)
    {
        printf("Please choose the maximum level you would like to compute weight-1 forms for: ");
        int maxM = 1+itos(gp_read_stream(stdin));
        pari_sp ltop = avma;
        GEN database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
        for(int N=1; N<maxM; N++)
        {
            pari_printf("Computing level N=%ld\n", N);
            database = updateDatabaseForLevel(database, N, maxM, 0);
            database = gerepilecopy(ltop, database);
        }
        while(1)
        {
            printf("Pick a level: ");
            GEN N=gp_read_stream(stdin);
            printf("Pick a conrey exponent for a character of that level: ");
            GEN chiexp=gp_read_stream(stdin);
            getFormDetails(N, chiexp, database);
            /*int dimension = wt1newformDimFromExp(N, chiexp, database);
            pari_printf("The dimension of S_1^new(%Ps,chi_%c) is %ld\n", N, getLMFDBlabel(N,chiexp), dimension);*/
        }
    }
    if(mode==222)
    {
        printf("Please choose a maximum level to verify all weight-1 dimension computations up to: ");
        int maxM = 1+itos(gp_read_stream(stdin));
        pari_sp ltop = avma;
        for(int N=1; N<maxM; N++)
        {
            GEN database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
            database = updateDatabaseForLevel(database, N, maxM, 0);
            GEN group = znstar0(stoi(N),1);
            GEN chars = getAllCharStats(N);
            for(int i=1; i<lg(chars); i++)
            {
                int parisComputedDimension = itos(mfdim(mkvec3(stoi(N),gen_1,mkvec2(group,gel(chars,i))), 0));
                int myComputedDimension = wt1newformdimension(N, gel(chars,i), database);
                if(parisComputedDimension != myComputedDimension)
                {
                    pari_printf("Oops! For level %ld and character %Ps pari computes dimension %ld but I computed dimension %ld\n", N, gel(chars,i), parisComputedDimension, myComputedDimension);
                    return 0;
                }
            }
            pari_printf("All computed dimensions up to level %ld are correct.\n",N);
            set_avma(ltop);
        }
        return 1;
    }
    if(mode==3)
    {
        printf("Please choose the level you would like to compute weight-1 forms for: ");
        int maxM = itos(gp_read_stream(stdin));
        GEN database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
        updateDatabaseForLevel(database, maxM, maxM, 1);
    }
     //Mode 4 times my computation
    if(mode==4)
    {
        while(1)
        {
            printf("Please select a maximum level to time computation up to: ");
            int maxM = 1+itos(gp_read_stream(stdin));
            pari_sp ltop = avma;

            clock_t before = clock();
            for(int N=1; N<maxM; N++)
            {
                GEN database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
                pari_printf("Performing computations for level N=%ld\n", N);
                database = updateDatabaseForLevel(database, N, maxM, 0);
                set_avma(ltop);
            }

            clock_t difference = clock() - before;
            int myTime = difference / CLOCKS_PER_SEC;
            if(myTime<120){
            pari_printf("Computing up to level %ld took %ld seconds.\n", maxM-1, myTime);
            } else {
            pari_printf("Computing up to level %ld took %ld minutes and %ld seconds.\n", maxM-1, myTime/60, myTime%60);
            }
        }
    }

    //Modes 5 and 6 compute, and validate, specific levels. This requires computation of divisor levels first.
    if(mode==5)
    {
        printf("Please choose the level you would like to compute weight-1 forms for: ");
        int maxM = itos(gp_read_stream(stdin));
        GEN divs = divisorsu(maxM);
        pari_sp ltop = avma;
        GEN database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
        for(int i=1; i<lg(divs); i++)
        {
            int N = divs[i];
            pari_printf("Computing level N=%ld\n", N);
            database = updateDatabaseForLevel(database, N, maxM, 0);
            database = gerepilecopy(ltop, database);
        }
        while(1)
        {
            pari_printf("Pick a conrey exponent for level %ld: ", maxM);
            GEN chiexp=gp_read_stream(stdin);
            getFormDetails(stoi(maxM), chiexp, database);
        }
    }
    if(mode==6)
    {
        printf("Please choose the maximum level you would like to validate weight-1 forms for: ");
        int maxM = itos(gp_read_stream(stdin));
        GEN divs = divisorsu(maxM);
        pari_sp ltop = avma;
        GEN database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
        int N;
        for(int i=1; i<lg(divs); i++)
        {
            N = divs[i];
            pari_printf("Computing level N=%ld\n", N);
            database = updateDatabaseForLevel(database, N, maxM, 0);
            database = gerepilecopy(ltop, database);
        }
        pari_printf("Checking computations.\n");
        GEN group = znstar0(stoi(N),1);
        GEN chars = getAllCharStats(N);
        for(int i=1; i<lg(chars); i++)
        {
            int parisComputedDimension = itos(mfdim(mkvec3(stoi(N),gen_1,mkvec2(group,gel(chars,i))), 0));
            int myComputedDimension = wt1newformdimension(N, gel(chars,i), database);
            if(parisComputedDimension != myComputedDimension)
            {
                pari_printf("Oops! For level %ld and character %Ps pari computes dimension %ld but I computed dimension %ld\n", N, gel(chars,i), parisComputedDimension, myComputedDimension);
                return 0;
            }
        }
        pari_printf("All computed dimensions for level %ld are correct.\n",N);
    }

    if(mode==7){
        char filename[30];
        FILE *out_file = fopen("wt1_form_dims.txt", "w");
        FILE *command_file = fopen("processcommands.txt", "w");
        printf("Please choose the maximum level you would like to generate a dimension file for: ");
        int maxM = itos(gp_read_stream(stdin));
        GEN database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
        pari_sp ltop = avma;
        for(long N=23; N<=maxM; N++)
        {
            pari_printf("processing level %ld\n", N);
            sprintf(filename, "wt1spaces/%ld.txt", N);
            FILE *in_file = fopen(filename, "r");
            if(in_file != NULL){
            gel(gel(database,1),N) = gp_read_file(filename);
            fclose(in_file);
            }
            GEN chars = getAllCharStats(N);
            for(int i=1; i<lg(chars); i++)
            {
                long dimension = wt1newformdimension(N, gel(chars,i), database);
                if(dimension!=0){
                    pari_fprintf(out_file, "%ld:%Ps:%ld\n", N,gel(chars,i),dimension);
                }
            }
            if(hasExotic(N, dihedralDims)){
                pari_printf("here with level %ld\n", N);
                pari_fprintf(command_file, "./a.out %ld 0\n", N);
            }
            set_avma(ltop);
        }
        fclose(out_file);
        fclose(command_file);
    }

    if(mode==8){
            printf("Please choose the maximum level you would like to convert dihedral dimensions for: ");
            int maxM = itos(gp_read_stream(stdin));

    char fname[30] = "odd_dihedral_dims_D.txt";
    FILE *out_file = fopen("wt1_conrey_dihedral_dims.txt", "w"); // write only
    FILE *fptr = NULL;

    fptr = fopen(fname, "r");

    if (fptr == NULL)
    {
        printf("Error! Could not open file\n");
        return 0;
    }
    char line[500];
    char sub[50];
    int position = 0;
    while(fgets(line, 500, fptr))
    {
        char *attrPtr = &line[0];
        char qolon = '.';//character to search
        char *quotPtr = strchr(attrPtr, qolon);
            position = quotPtr - attrPtr;
            int c = 0;
            while (c < position)
            {
                sub[c] = line[c];
                c++;
            }
            sub[c] = '\0';
            int lev = atoi(sub);
            if(lev>maxM) break;
            c = position+3;
            while (line[c]!='.')
            {
                c++;
            }
            position = ++c;
            while (line[c]!=':')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            int conreyExp = atoi(sub);

            position = ++c;
            while (line[c]!=':')
            {
                sub[c-position] = line[c];
                c++;
            }
            sub[c-position] = '\0';
            int dihedralDimension = atoi(sub);
            GEN group = znstar0(stoi(lev),1);

            int order = itos(zncharorder(group, stoi(conreyExp)));
            dihedralDimension/=eulerphiu(order);

            while (line[c]!='[')
            {
                c++;
            }
            c++;
            while (line[c]!='[')
            {
                c++;
            }



            GEN Dlcm = cgetg(1,t_VEC);
            while (line[c]!=']'){
                position = ++c;
                while (line[c]!=']' && line[c]!= ','){
                    sub[c-position] = line[c];
                    c++;
                }
                sub[c-position] = '\0';
                long Dimage = atoi(sub);
                if(ZV_search(Dlcm, stoi(Dimage))==0){
                    Dlcm = vec_append(Dlcm, stoi(Dimage));
                    ZV_sort_inplace(Dlcm);
                }
            }

            GEN conrLog = bestRep(group, znconreychar(group, stoi(conreyExp)));
            pari_printf("printing %ld.1.%Ps:%ld:%Ps\n", lev, conrLog, dihedralDimension, Dlcm);
            pari_fprintf(out_file, "%ld.1.%Ps:%ld:%Ps\n", lev, conrLog, dihedralDimension, Dlcm);

        }
        fclose(out_file);
        return 1;
    }
    if(mode==9){
        while(1){
        printf("Please choose the level you would like to verify the wt2 computation for: ");
            int lev = itos(gp_read_stream(stdin));
        int correct = verifywt2(lev);
        pari_printf("Correct? %ld\n", correct);
        }
    }
    if(mode==10){
        printf("Please choose the start level you would like to verify the wt2 computation for: ");
        int startM = itos(gp_read_stream(stdin));
        printf("Please choose the maximum level you would like to verify the wt2 computation for: ");
        int maxM = 1+itos(gp_read_stream(stdin));
        for(int i = startM; i<maxM; i++){
                pari_printf("checking %ld\n", i);
        int correct = verifywt2(i);
        if(!correct){
            pari_printf("whoops at %ld\n", i);
            return 0;
        }
        }
        pari_printf("all correct!\n");
    }
    if(mode==11){
        printf("Please choose the level you would like to compute a trace for: ");
        int N = itos(gp_read_stream(stdin));
        printf("Please choose the coeff of the traceform you would like: ");
        int n = itos(gp_read_stream(stdin));
        specifTrace(N, n);
    }
    if(mode==12)
    {
        pari_sp ltop = avma;
        char fname[30] = "wt1correctdims.txt";
        FILE *fptr = NULL;
        fptr = fopen(fname, "r");
        int minM = 1;
        char line[200];
        while(fgets(line, 200, fptr))
        {
            GEN correct = gp_read_str(line);
            if(itos(gel(correct,1))<=minM) {
                minM = itos(gel(correct,1))+1;
            }
        }
        fclose(fptr);
        printf("Please choose a maximum level to generate a correct dimensions file up to: ");
        int maxM = 1+itos(gp_read_stream(stdin));
        FILE *out_file = fopen("wt1correctdims.txt", "a");
        set_avma(ltop);

        for(int N=minM; N<maxM; N++)
        {
            GEN group = znstar0(stoi(N),1);
            GEN chars = getAllCharStats(N);
            for(int i=1; i<lg(chars); i++)
            {
                pari_sp lmed = avma;
                int parisComputedDimension = itos(mfdim(mkvec3(stoi(N),gen_1,mkvec2(group,gel(chars,i))), 0));
                pari_fprintf(out_file, "%Ps\n", mkvec3(stoi(N),gel(chars,i),stoi(parisComputedDimension)));
                set_avma(lmed);
            }
            pari_printf("Generated up to level %ld\n",N);
            set_avma(ltop);
        }
        fclose(out_file);
        return 1;
    }
    if(mode==2)
    {
        char fname[30] = "wt1correctdims.txt";
        FILE *fptr = NULL;
        fptr = fopen(fname, "r");

        printf("Please choose a maximum level to verify all weight-1 dimension computations up to: ");
        int maxM = 1+itos(gp_read_stream(stdin));
        pari_sp ltop = avma;
        char line[100];
        int N = 0;
        GEN database;
        while(fgets(line, 100, fptr))
        {
            GEN correct = gp_read_str(line);
            if(itos(gel(correct,1))==maxM) return 1;
            while(itos(gel(correct,1))>N){
                    pari_printf("All computed dimensions up to level %ld are correct.\n",N);
                    N++;
                    database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
                    char filename[20];
                    sprintf(filename, "wt1spaces/%d.txt", N);
                    FILE *in_file = fopen(filename, "r");
                    if(in_file != NULL){
                        gel(gel(database,1),N) = gp_read_file(filename);
                        fclose(in_file);
                    }
            }
            int parisComputedDimension = itos(gel(correct,3));
            int myComputedDimension = wt1newformdimension(N, gel(correct,2), database);
                if(parisComputedDimension != myComputedDimension)
                {
                    pari_printf("Oops! For level %ld and character %Ps pari computes dimension %ld but I computed dimension %ld\n", N, gel(correct,2), parisComputedDimension, myComputedDimension);
                    return 0;
                }
            set_avma(ltop);
        }
        pari_printf("All computed dimensions up to level %ld are correct.\n",maxM-1);
        return 1;
    }
    if(mode==14)
    {
        GEN correct;
        char fname[30] = "wt1correctdims.txt";
        FILE *fptr = NULL;
        fptr = fopen(fname, "r");
        char line[100];
        int N = 1;
        int hasSomething = 0;
        GEN database = cgetg(1,t_VEC);
        while(fgets(line, 100, fptr))
        {
            correct = gp_read_str(line);
            if(itos(gel(correct,1))>N){
                if(!hasSomething){
                    database = vec_append(database, stoi(N));
                } else {
                hasSomething = 0;
                }
                N++;
            }
            if (itos(gel(correct,3))>getDihedralDim(N, gel(correct,2), dihedralDims)){
                hasSomething = 1;
            }
        }
        FILE *out_file = fopen("wt1hasnothing.txt", "w");
        pari_fprintf(out_file, "%Ps\n", database);
        return 1;
    }
    if (mode==99){
        while(1)
        {
            printf("Please select a maximum level to time computation up to: ");
            int maxM = 1+itos(gp_read_stream(stdin));
            pari_sp ltop = avma;

            clock_t before = clock();
            FILE *num_file = fopen("calcupto.txt", "r");
            flock(fileno(num_file), LOCK_EX);
            int N = itos(gp_read_stream(num_file));
            fclose(num_file);
            FILE *out_file = fopen("calcupto.txt", "w");
                pari_fprintf(out_file, "%ld", N+1);
                fclose(out_file);
            for(; N<maxM;)
            {
                GEN database = mkvec3(zerovec(maxM), zerovec(maxM), dihedralDims);
                pari_printf("Performing computations for level N=%ld\n", N);
                database = updateDatabaseForLevel(database, N, maxM, 0);
                set_avma(ltop);
                num_file = fopen("calcupto.txt", "r");
                flock(fileno(num_file), LOCK_EX);
            N = itos(gp_read_stream(num_file));
            fclose(num_file);
            out_file = fopen("calcupto.txt", "w");
                pari_fprintf(out_file, "%ld", N+1);
                flock(fileno(num_file), LOCK_UN);
                fclose(out_file);
            }

            clock_t difference = clock() - before;
            int myTime = difference / CLOCKS_PER_SEC;
            if(myTime<120){
            pari_printf("Computing up to level %ld took %ld seconds.\n", maxM-1, myTime);
            } else {
            pari_printf("Computing up to level %ld took %ld minutes and %ld seconds.\n", maxM-1, myTime/60, myTime%60);
            }
        }

    }

    if (mode==100){
        long RAMallowed = 15000000000;
        printf("Please select a maximum level to aim for: ");
        int maxM = 1+itos(gp_read_stream(stdin));
        FILE *files[3];
        FILE *out_file1 = fopen("commands1", "w");
        FILE *out_file2 = fopen("commands2", "w");
        FILE *out_file3 = fopen("commands3", "w");
        files[0] = out_file1;
        files[1] = out_file2;
        files[2] = out_file3;
        for(long i = -62; i<2000; i++)
        {
            pari_fprintf(files[0], "./a.out %ld %ld %ld\n", maxM, i, RAMallowed);
        }
        for(long i = -126; i<-62; i++){
            pari_fprintf(files[1], "./a.out %ld -50\n", maxM);
            pari_fprintf(files[2], "./a.out %ld -50\n", maxM);
        }
        for(long i = 2000; i<3000; i++){
            long index = random_Fl(2);
            pari_fprintf(files[index], "./a.out %ld %ld %ld\n", maxM, i, RAMallowed);
        }
        for(long i = 3000; i<maxM; i++){
            long index = random_Fl(3);
            pari_fprintf(files[index], "./a.out %ld %ld %ld\n", maxM, i, RAMallowed);
        }
        fclose(files[0]);
        fclose(files[1]);
        fclose(files[2]);
        }

        if (mode==101){
            printf("Please select the level currently done up to: ");
            long minM = 1+itos(gp_read_stream(stdin));
            printf("Please select a maximum level to compute correct dimensions for: ");
            long maxM = 1+itos(gp_read_stream(stdin));
            FILE *out_file = fopen("commands", "w");
            for(long i = minM; i<maxM; i++)
            {
                pari_fprintf(out_file, "./a.out %ld\n", i);
            }
            fclose(out_file);
        }

        if (mode==102){
                for(long N = 1; N<100000; N++){
                    pari_sp ltop = avma;
                    char filename[30];
                    sprintf(filename, "wt1correctdims/%ld.txt", N);
                    FILE *fptr = fopen(filename, "r");
                    if(fptr == NULL) {
                            return 0;
                    }
                    sprintf(filename, "wt1spaces/%ld.txt", N);
                    GEN database = mkvec3(zerovec(N), zerovec(N), dihedralDims);
                    FILE *in_file = fopen(filename, "r");
                    if(in_file != NULL){
                        gel(gel(database,1),N) = gp_read_file(filename);
                        fclose(in_file);
                    }
                    char line[100];
                    while(fgets(line, 100, fptr))
        {
            GEN correct = gp_read_str(line);
            int parisComputedDimension = itos(gel(correct,3));
            int myComputedDimension = wt1newformdimension(N, gel(correct,2), database);
                if(parisComputedDimension != myComputedDimension)
                {
                    pari_printf("Oops! For level %ld and character %Ps pari computes dimension %ld but I computed dimension %ld\n", N, gel(correct,2), parisComputedDimension, myComputedDimension);
                    return 0;
                }
        }

            set_avma(ltop);
            fclose(fptr);
            pari_printf("All computed dimensions up to level %ld are correct\n", N);

        }
        }

    if (mode==999){
        long RAMallowed = 50000000000;
        FILE *out_file = fopen("finalcommands", "w");
        printf("Should be up to?:");
        int maxM = itos(gp_read_stream(stdin));
        pari_sp av = avma;
        for(int N = 26; N<=maxM; N++){
        int willcompsomething = 0;
            GEN stats = getAltCharStats(N);

        for (long i = 1; i<lg(stats); i++)
    {
        int exoticLift = canHaveExotic(N, gel(stats,i));
        //If we cannot lift to a level with exotics, don't need to compute
        if (!exoticLift) continue;
        //If the nearest lift to a space with possible exotics is beyond what we're aiming for,
        //and we know the dihedrals are at this level, no need to compute
        if(N<lg(dihedralDims) && N>maxM/exoticLift)
        {
            continue;
        }
        //If the space itself cannot have exotics and there are no dihedral forms, no need to compute
        if(exoticLift>1 && !getDihedralDim(N, gel(stats,i), dihedralDims))
        {
            continue;
        }
        willcompsomething = 1;
        break;
    }
    if (!willcompsomething) continue;
         char filename[20];
        sprintf(filename, "wt1spaces/%d.txt", N);
        FILE *in_file = fopen(filename, "r");
        if(in_file == NULL){
            pari_printf("didn't get %ld\n", N);
            pari_fprintf(out_file, "./a.out %ld %ld %ld\n", maxM, N, RAMallowed);
        } else {
            fclose(in_file);
        }
        set_avma(av);
        }
        fclose(out_file);
    }


}
//Time comparison:
//400: 28 vs 34 vs 14
//450: 70 vs 55 vs 25
//500: 102 vs 84 vs 39
//550: 258 vs 124 vs 59
//600: 284 vs 183 vs 95
//650: 1065 vs 272 vs 131
//700: 1986 vs 374 vs 185
//750: 3002 vs 485 vs 272
//800: 354
//850: 477
//900: 698
//950: 899
//1000: 5m34s
