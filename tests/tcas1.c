
/*  -*- Last-Edit:  Fri Jan 29 11:13:27 1993 by Tarak S. Goradia; -*- */
/* $Log: tcas.c,v $
 * Revision 1.2  1993/03/12  19:29:50  foster
 * Correct logic bug which didn't allow output of 2 - hf
 * */

#include <stdio.h>
#include <assert.h>

#define OLEV       600		/* in feets/minute */
#define MAXALTDIFF 600		/* max altitude difference in feet */
#define MINSEP     300          /* min separation in feet */
#define NOZCROSS   100		/* in feet */
#define OLEV_correct       600    /* in feets/minute */
#define MAXALTDIFF_correct 600    /* max altitude difference in feet */
#define MINSEP_correct     300          /* min separation in feet */
#define NOZCROSS_correct   100    /* in feet */
				/* variables */

// typedef int bool;

int Cur_Vertical_Sep;
int High_Confidence;
int Two_of_Three_Reports_Valid;

int Own_Tracked_Alt;
int Own_Tracked_Alt_Rate;
int Other_Tracked_Alt;

int Alt_Layer_Value;		/* 0, 1, 2, 3 */
int Positive_RA_Alt_Thresh;

int Up_Separation;
int Down_Separation;

				/* state variables */
int Other_RAC;			/* NO_INTENT, DO_NOT_CLIMB, DO_NOT_DESCEND */
#define NO_INTENT 0
#define DO_NOT_CLIMB 1
#define DO_NOT_DESCEND 2
#define NO_INTENT_correct 0
#define DO_NOT_CLIMB_correct 1
#define DO_NOT_DESCEND_correct 2

int Other_Capability;		/* TCAS_TA, OTHER */
#define TCAS_TA 1
#define OTHER 2
#define TCAS_TA_correct 1
#define OTHER_correct 2

int Climb_Inhibit;		/* true/false */

#define UNRESOLVED 0
#define UPWARD_RA 1
#define DOWNWARD_RA 2
#define UNRESOLVED_correct 0
#define UPWARD_RA_correct 1
#define DOWNWARD_RA_correct 2

//bat
int  ALIM();
int  Inhibit_Biased_Climb();
int   Non_Crossing_Biased_Climb();
int   Non_Crossing_Biased_Descend();
int   Own_Below_Threat();
int   Own_Above_Threat();
int  alt_sep_test();

void initialize()
{
    Positive_RA_Alt_Thresh = 740;
}

int ALIM ()
{
 return Positive_RA_Alt_Thresh;
}

int Inhibit_Biased_Climb ()
{
    int result; 
    if (Climb_Inhibit) result = Up_Separation + NOZCROSS; else result = Up_Separation;
    return result; 
}

int Non_Crossing_Biased_Climb()
{
    int upward_preferred;
    int upward_crossing_situation;
    int result;
    
    int own_below_threat = Own_Below_Threat(); 
    int own_above_threat = Own_Above_Threat(); 
    //upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (Inhibit_Biased_Climb() > Down_Separation)
    {
	if ((own_below_threat==0) || ((own_below_threat==1) && (!(Down_Separation > ALIM())))) result = 1; 
	else result = 0;
    }
    else
    {	
	if ((own_above_threat==0) && ((Cur_Vertical_Sep >= MINSEP) && (Up_Separation >= ALIM()))) result = 1; 
	else result = 0;
    }
    return result;
}

int Non_Crossing_Biased_Descend()
{
    int upward_preferred;
    int upward_crossing_situation;
    int result;

    int own_below_threat = Own_Below_Threat(); 
    int own_above_threat = Own_Above_Threat();
    //upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (Inhibit_Biased_Climb() > Down_Separation)
    {
	if ((own_below_threat==1) && (Cur_Vertical_Sep >= MINSEP) && (Down_Separation >= ALIM())) result = 1; 
	else result = 0;
    }
    else
    {
	if ((own_below_threat==0) || ((own_above_threat==1) && (Up_Separation >= ALIM()))) result = 1; 
	else result = 0;
    }
    return result;
}

int Own_Below_Threat()
{
    int result; 
    if ((Own_Tracked_Alt < Other_Tracked_Alt)) result = 1; 
	else result = 0;
    return result;
}

int Own_Above_Threat()
{
    int result; 
    if ((Other_Tracked_Alt < Own_Tracked_Alt)) result = 1; 
	else result = 0;
    return result;
}

int alt_sep_test()
{
    int enabled, tcas_equipped, intent_not_known;
    int need_upward_RA, need_downward_RA;
    int alt_sep;

    if ((High_Confidence==1) && ((Own_Tracked_Alt_Rate <= OLEV) && (Cur_Vertical_Sep > MAXALTDIFF))) enabled=1;
    else enabled=0; 
    if (Other_Capability == TCAS_TA) tcas_equipped=1;
    else tcas_equipped=0; 
    if ((Two_of_Three_Reports_Valid==1) && (Other_RAC == NO_INTENT)) intent_not_known=1; 
    else intent_not_known=0; 
    
    alt_sep = UNRESOLVED;
    
    if ((enabled==1) && (((tcas_equipped==1) && (intent_not_known==1)) || (tcas_equipped==0)))
    {
	if ((Non_Crossing_Biased_Climb()==1) && (Own_Below_Threat()==1)) need_upward_RA = 1; 
	else need_upward_RA = 0; 
	if ((Non_Crossing_Biased_Descend()==1) && (Own_Above_Threat()==1)) need_downward_RA = 1;
	else need_downward_RA = 0; 
	if ((need_upward_RA == 1) && (need_downward_RA == 1))
        /* unreachable: requires Own_Below_Threat and Own_Above_Threat
           to both be true - that requires Own_Tracked_Alt < Other_Tracked_Alt
           and Other_Tracked_Alt < Own_Tracked_Alt, which isn't possible */
	    alt_sep = UNRESOLVED;
	else if (need_upward_RA == 1) {
	    alt_sep = UPWARD_RA;	     
	    }
	else if (need_downward_RA == 1)
	    alt_sep = DOWNWARD_RA;
	else
	    alt_sep = UNRESOLVED;
    }
    assert ((need_upward_RA <= 0) || (Down_Separation >= Positive_RA_Alt_Thresh));
    return alt_sep;
}



void main() {
    Cur_Vertical_Sep = __VERIFIER_nondet_int();// = atoi(argv[1]);
    High_Confidence = [0,1];// = atoi(argv[2]);
    //__CPROVER_assume(High_Confidence>=0 && High_Confidence<=1);
    Two_of_Three_Reports_Valid = [0,1];// = atoi(argv[3]);
    //__CPROVER_assume(Two_of_Three_Reports_Valid>=0 && Two_of_Three_Reports_Valid<=1);
    Own_Tracked_Alt = __VERIFIER_nondet_int();// = atoi(argv[4]);
    Own_Tracked_Alt_Rate = __VERIFIER_nondet_int();// = atoi(argv[5]);
    Other_Tracked_Alt = __VERIFIER_nondet_int();// = atoi(argv[6]);
    Alt_Layer_Value = [0,3];// = atoi(argv[7]);
    //__CPROVER_assume(Alt_Layer_Value>=0 && Alt_Layer_Value<=3);
    Up_Separation = __VERIFIER_nondet_int();// = atoi(argv[8]);
    Down_Separation = __VERIFIER_nondet_int();// = atoi(argv[9]);
    Other_RAC = [0,1];// = atoi(argv[10]);
    //__CPROVER_assume(Other_RAC>=0 && Other_RAC<=1);
    Other_Capability = [0,1];// = atoi(argv[11]);
    //__CPROVER_assume(Other_Capability>=0 && Other_Capability<=1);
    Climb_Inhibit = [0,1];// = atoi(argv[12]);
    //__CPROVER_assume(Climb_Inhibit>=0 && Climb_Inhibit<=1);
    //__CPROVER_assume(Own_Tracked_Alt<=100000 && Other_Tracked_Alt<=100000 && Up_Separation<=100000 && Down_Separation<=100000 && Cur_Vertical_Sep<=100000 && Own_Tracked_Alt_Rate<=100000);
    //__CPROVER_assume(Own_Tracked_Alt>=0 && Other_Tracked_Alt>=0 && Up_Separation>=0 && Down_Separation>=0 && Cur_Vertical_Sep>=0 && Own_Tracked_Alt_Rate>=0);

    initialize();
    int res = alt_sep_test();

}
//</ASSUME_CORRECT>
