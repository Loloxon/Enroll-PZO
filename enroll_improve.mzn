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
%% nieprzekraczalne 
% int: being_late_treshold;
%% mnożymy ilość minut razy late_to_disappointment_multiplier 
% int: late_to_disappointment_multiplier;
%% przerwa w minutach razy break_to_disappointment_multiplier 
% int: break_to_disappointment_multiplier;

%sety zrobione z wartości wyżej
set of int: Student = 1..n_students;
set of int: Class = 1..n_classes;
set of int: Group = 1..n_groups;
set of int: Day = 1..n_days;
set of int: Location = 1..n_locations;
set of int: Time = 0..n_time_units_in_hour * 24;


set of int: Preference = exclusion..max([student_prefers[s,g] | s in Student, g in Group]);

%info o studentach
% array[Student] of bool: student_can_teleport;
% array[Student] of bool: student_loves_breaks;
array[Student] of 0..5: student_break_importance;
array[Student, Group] of int: student_prefers;

function var int: ceil_div(var int: x, var int: y) =
  x div y + ((x mod y) > 0);

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%time range
int: start = min(group_start);
int: end = max(group_start) + max(class_duration);
% int: maxObjective = pow(max([student_prefers[s,g] | s in Student, g in Group]) + end*n_days*break_to_disappointment_multiplier + end*n_days*late_to_disappointment_multiplier,2)*n_students;
int: maxObjective = 100000000;
%niezadowolenie z przydziału grup do zminimalizowania
% array[Student] of var Preference : preference_disappointment = [sum([best_preferences[S,C] - got_preferences[S,C]| C in Class]) | S in Student];  
array[Student] of var int : preference_disappointment = [bestPref[S] - gotPref[S] | S in Student];
% array[Student, Class] of Preference : best_preferences = array2d(Student, Class, 
%     [max([if group_class[G] = C then student_prefers[S,G] else -1 endif | G in Group]) | S in Student, C in Class]);
array[Student] of var int: bestPref = [sum([max([if group_class[G] = C then student_prefers[S,G] else 0 endif | G in Group]) | C in Class]) |S in Student];
% array[Student, Class] of var Preference : got_preferences = array2d(Student, Class, 
%     [if GroupAssignment[S,C] != 0 then student_prefers[S,GroupAssignment[S,C]] else -1 endif | S in Student, C in Class]);
array[Student] of var int: gotPref = [sum([max([if GroupAssignmentB[S,G] /\ group_class[G] = C then student_prefers[S,G] else 0 endif | G in Group]) | C in Class]) |S in Student];
% niezadowolenie z powodu przerw
array[Student] of var int : break_disappointment = [sum([staying_at_uni[S,D] - length_of_lessons[S,D] | D in Day]) | S in Student];

array[Student] of var int: normalized_break_disappointment =
[ceil_div(break_disappointment[S],n_time_units_in_hour)| S in Student];

array[Student, Day] of var 0..end : staying_at_uni = array2d(Student, Day,
    [max(max([if GroupAssignmentB[S,G] /\ group_day[G] == D
                                       then group_start[G] + class_duration[group_class[G]]
                                       else 0 endif 
                        | G in Group])
       - min([if GroupAssignmentB[S,G] /\ group_day[G] == D 
                                       then group_start[G] 
                                       else n_time_units_in_hour * 24 endif 
                        | G in Group]),0)
                 | S in Student, D in Day]);

array[Student, Day] of var 0..end : length_of_lessons; 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%               here starts new stuff               %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% array[1..n_students*n_groups] of 0..n_groups: assignment;
array[Student] of set of Group: assignment;

array[Student, Group] of var bool: GroupAssignmentB;
% constraint forall(S in Student, G in Group)(if assignment[(S-1)*n_groups+G]>0 then GroupAssignmentB[S,G] = true else GroupAssignmentB[S,G] = false endif);
constraint forall(S in NewStudent, G in NewGroup)(if exists(G1 in assignment[S])(G1=G) then GroupAssignmentB[S,G]=true else GroupAssignmentB[S,G]=false endif);
set of int: NewStudent = 1..n_students-5;
set of int: NewGroup = 1..n_groups;


constraint forall(S in Student, D in Day)(length_of_lessons[S,D] = sum([
if GroupAssignmentB[S,G] /\ group_start[G]<=T /\ group_start[G]+class_duration[group_class[G]]-1>=T 
then 1 else 0 endif | G in Group where group_day[G]=D, T in start..end]));
    
var 0..maxObjective : objective = sum([pow(ceil_div(student_break_importance[S] * normalized_break_disappointment[S] + (10 - student_break_importance[S]) * preference_disappointment[S],10),2) | S in Student]);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%             here are restrictions             %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(S in Student, G in Group)(if student_prefers[S,G]=-1 then GroupAssignmentB[S,G] = false endif);

predicate overlap_in_time(var Group: G1, var Group: G2) = group_day[G1] = group_day[G2] /\
        group_start[G1]+class_duration[group_class[G1]]>group_start[G2] /\ group_start[G1]<group_start[G2]+class_duration[group_class[G2]];

constraint forall(S in Student, C in Class)(if attends[S,C]
then exists(G in Group where group_class[G] = C)(GroupAssignmentB[S,G]=true) endif);

array[Student, Class] of var bool: attends;
constraint forall(S in Student, C in Class)(if not forall(G in Group where group_class[G] = C)(student_prefers[S,G]=-1)
then attends[S,C]=true else attends[S,C]=false endif);

array[Group,Group] of var 0..1: cohabited;
constraint forall(G1, G2 in Group)(if exists(GC in GroupCohabitats, GC1, GC2 in group_cohabitats[GC])(G1=GC1 /\ G2=GC2 \/ G1=GC2 /\ G2=GC1) then cohabited[G1,G2] = true /\ cohabited[G2,G1] = true else cohabited[G1,G2] = false /\ cohabited[G2,G1] = false endif);

constraint forall(S in Student, G1, G2 in Group where G1<G2 /\ GroupAssignmentB[S,G1] /\ GroupAssignmentB[S,G2])(
not overlap_in_time(G1, G2)
\/ exists(G in GroupCohabitats)({G1, G2}=group_cohabitats[G])
);

constraint forall(G in Group)(sum(S in Student)(GroupAssignmentB[S,G])<=class_size[group_class[G]]);
constraint forall(S in Student, C in Class)(sum(G in Group where group_class[G]=C)(GroupAssignmentB[S,G])<=1);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
solve 
      :: seq_search([
        int_search(GroupAssignmentB, dom_w_deg, indomain_random),
        ])
%         satisfy;
        minimize objective;

output 
%       [show([show([coexists[S,C1,C2] | C1, C2 in Class]) | S in Student]) ++ "\n"] ++ 
%       [show([show([length_of_lessons2[S,C] | C in Class]) | S in Student]) ++ "\n"] ++
%       [show([counted[S,C] | S in Student, C in Class]) ++ "\n"] ++ 
      ["assignment = [" ++ join(",", ["{" ++ join(", ", [show(g) |  g in Group where fix(GroupAssignmentB[s,g])]) ++ "}" | s in Student]) ++ "];\n"] ++
%       ["assignment = [" ++ join(",", ["{" ++ join(", ", show([ if GroupAssignment[s,g]!=0 then g else "" endif |  g in Group])) ++ "}" | s in Student]) ++ "];\n"]
%      ["assignment = " ++ show([GroupAssignment[s,c]| c in Class, s in Student]) ++ ";\n"] ++
%     ++ ["time spent at univer: " ++ show([staying_at_uni[S,D] | S in Student, D in Day]) ++ "\n"]
%     ++ ["length of lessons:    " ++ show([length_of_lessons[S,D] | S in Student, D in Day]) ++ "\n"]     
    ["total_break_disappointment = " ++ show(sum([normalized_break_disappointment[S] | S in Student])) ++ ";\n"]
%     ++ ["best possible preferences: " ++ show([best_preferences[S,C] | S in Student, C in Class]) ++ "\n"] 
%     ++ ["preferences which got:     " ++ show([got_preferences[S,C] | S in Student, C in Class]) ++ "\n"]
    ++ ["total_preference_disappointment = " ++ show(sum(preference_disappointment)) ++ ";\n"]
    ++ ["objective = " ++ show(objective) ++ ";\n"]
%     ++ [show([x | x in group_cohabitats[1]])]
%     ++ [show([if cohabited[G1,G2] = 1 then show([G1,G2]) else "" endif | G1, G2 in Group])]
%     ++ [show([show(sum([if 
%     exists(G in Group)(GroupAssignment[S,group_class[G]]=G /\ group_day[G]=D /\ group_start[G]<=T /\ group_start[G]+class_duration[group_class[G]]>T)
%     then 1 else 0 endif | T in start..end])) ++ "\n"| S in Student, D in Day])]
    
