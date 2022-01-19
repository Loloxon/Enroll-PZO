% Parameters
%ilosc studentów
int: n_students;
%ilość dni
int: n_days;
%ilość przedmiotów
int: n_classes;
%ilość wszystkich grup
int: n_groups;
%ilość budynków
int: n_locations;
%ilość jednostek czasu w godzinie
int: n_time_units_in_hour;
%wartość oznaczająca nie chodzenie na przedmiot
int: exclusion = -1;
%sety zrobione z wartości wyżej
set of int: Student = 1..n_students;
set of int: Class = 1..n_classes;
set of int: Group = 1..n_groups;
set of int: Day = 1..n_days;
set of int: Location = 1..n_locations;
set of int: Time = 0..n_time_units_in_hour * 24;


set of int: Preference = exclusion..max([student_prefers[s,g] | s in Student, g in Group]);

%info o studentach
array[Student] of 0..5: student_break_importance;
array[Student, Group] of int: student_prefers;

function var int: ceil_div(var int: x, var int: y) =
  x div y + ((x mod y) > 0);

% predicate overlap_in_time(var Group: G1, var Group: G2) = group_day[G1] = group_day[G2] /\
%         group_start[G1]+class_duration[group_class[G1]]+travel_duration[group_location[G1],group_location[G2]]>group_start[G2] /\ group_start[G1]<group_start[G2]+class_duration[group_class[G2]]+travel_duration[group_location[G2],group_location[G1]];
predicate overlap_in_time(var Group: G1, var Group: G2) = group_day[G1] = group_day[G2] /\
        not(group_start[G1]+class_duration[group_class[G1]]+travel_duration[group_location[G1],group_location[G2]]<=group_start[G2] \/ group_start[G1]>=group_start[G2]+class_duration[group_class[G2]]+travel_duration[group_location[G2],group_location[G1]]);

array[Class] of Time: class_duration;
array[Class] of int: class_size;

%info o grupach
array[Group] of Class: group_class;
array[Group] of Time: group_start;
array[Group] of Location: group_location;
array[Group] of Day: group_day;
array[int] of set of Group: group_cohabitats;
%odległość między budynkami
array[Location, Location] of Time: travel_duration;

set of int: GroupCohabitats = 1..length(group_cohabitats);

int: M = 1000000;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%time range
int: start = min(group_start);
int: end = max(group_start) + max(class_duration);
% int: maxObjective = 300000;
int: maxObjective = 38000;
int: minObjective = 35000;
 
array[Student] of var 0..n_classes*max(student_prefers) : preference_disappointment = [bestPref[S] - gotPref[S] | S in Student];

array[Student] of var 0..n_classes*max(student_prefers): bestPref = [sum([max([if group_class[G] = C then student_prefers[S,G] else 0 endif | G in Group]) | C in Class]) |S in Student];

array[Student] of var 0..n_classes*max(student_prefers): gotPref = [sum([sum([if GroupAssignmentB[S,G]=1 /\ group_class[G] = C then student_prefers[S,G] else 0 endif | G in Group]) | C in Class]) |S in Student];
% niezadowolenie z powodu przerw
array[Student] of var 0..end*n_days : break_disappointment = [sum([staying_at_uni[S,D] - length_of_lessons[S,D] | D in Day]) | S in Student];

array[Student] of var 0..24*n_days: normalized_break_disappointment =
[ceil_div(break_disappointment[S],n_time_units_in_hour)| S in Student];

array[Student, Day] of var 0..end : staying_at_uni = array2d(Student, Day,
    [max(max([if GroupAssignmentB[S,G]=1 /\ group_day[G] == D
                                       then group_start[G] + class_duration[group_class[G]]
                                       else 0 endif 
                        | G in Group])
       - min([if GroupAssignmentB[S,G]=1 /\ group_day[G] == D 
                                       then group_start[G] 
                                       else n_time_units_in_hour * 24 endif 
                        | G in Group]),0)
                 | S in Student, D in Day]);

array[Student, Day] of var 0..end : length_of_lessons; 

% constraint forall(S in Student, D in Day)(length_of_lessons[S,D] = sum([
% if GroupAssignmentB[S,G]=1 /\ group_start[G]<=T /\ group_start[G]+class_duration[group_class[G]]-1>=T 
% then 1 else 0 endif | G in Group where group_day[G]=D, T in start..end]));
constraint forall(S in Student, D in Day)(length_of_lessons[S,D] = sum([GroupAssignmentB[S,G]
| G in Group where group_day[G]=D, T in start..end where group_start[G]<=T /\ group_start[G]+class_duration[group_class[G]]>T]));
    
var minObjective..maxObjective : objective = sum([pow(ceil_div(student_break_importance[S] * normalized_break_disappointment[S] + (10 - student_break_importance[S]) * preference_disappointment[S],10),2) | S in Student]);

array[Student, Class] of var 0..1: attends;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%               gettin static info               %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
array[Student] of set of Group: assignment;

array[Student, Group] of var 0..1: GroupAssignmentB;
constraint forall(S in Student where relaxS[S]=1, G in Group where relaxC[group_class[G]]=1)(if exists(G1 in assignment[S])(G1=G) then GroupAssignmentB[S,G]=1 else GroupAssignmentB[S,G]=0 endif);

array[Student] of 0..1: relaxS;
array[Class] of 0..1: relaxC;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%             constraints             %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% constraint forall(S in Student, G in Group)(if student_prefers[S,G]=-1 then GroupAssignmentB[S,G] = 0 endif);
constraint forall(S in Student, G in Group)(student_prefers[S,G] * GroupAssignmentB[S,G] >= 0);

% constraint forall(S in Student, C in Class)(if attends[S,C]=1
% then exists(G in Group where group_class[G] = C)(GroupAssignmentB[S,G]=1) endif);
constraint forall(S in Student, C in Class)(sum(G in Group where group_class[G] = C)(GroupAssignmentB[S,G])=attends[S,C]);

% constraint forall(S in Student, C in Class)(if not forall(G in Group where group_class[G] = C)(student_prefers[S,G]=-1)
% then attends[S,C]=1 else attends[S,C]=0 endif);
constraint forall(S in Student, C in Class)(if sum(G in Group where group_class[G]=C)(student_prefers[S,G])>=0
then attends[S,C]=1 else attends[S,C]=0 endif);

% albo nie nachodzą na siebie, albo są w cohabitats
constraint forall(S in Student, G1, G2 in Group where G1<G2 /\ GroupAssignmentB[S,G1]=1 /\ GroupAssignmentB[S,G2]=1)(not(
overlap_in_time(G1, G2)
/\ not exists(G in GroupCohabitats)({G1, G2}=group_cohabitats[G])));
% grupa nie przekracza liczebności
constraint forall(G in Group)(sum(S in Student)(GroupAssignmentB[S,G])<=class_size[group_class[G]]);
% każdy student tylko jedna grupa danego przedmiotu
constraint forall(S in Student, C in Class)(sum(G in Group where group_class[G]=C)(GroupAssignmentB[S,G])<=1);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
solve 
      :: seq_search([
        int_search(GroupAssignmentB, dom_w_deg, indomain_random),
        int_search(attends, dom_w_deg, indomain_random),
        ])
%         satisfy;
        minimize objective;

output 
    ["assignment = [" ++ join(",", ["{" ++ join(", ", [show(g) |  g in Group where fix(if GroupAssignmentB[s,g]=1 then true else false endif)]) ++ "}" | s in Student]) ++ "];\n"]
    ++ ["total_break_disappointment = " ++ show(sum([normalized_break_disappointment[S] | S in Student])) ++ ";\n"]
    ++ ["total_preference_disappointment = " ++ show(sum(preference_disappointment)) ++ ";\n"]
    ++ ["objective = " ++ show(objective) ++ ";\n"]
    
