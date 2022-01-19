% Parameters
int: n_students;
int: n_days;
int: n_classes;
int: n_groups;
int: n_locations;
int: n_time_units_in_hour;
int: exclusion = -1;

set of int: Student = 1..n_students;
set of int: Class = 1..n_classes;
set of int: Group = 1..n_groups;
set of int: Day = 1..n_days;
set of int: Location = 1..n_locations;
set of int: Time = 0..n_time_units_in_hour * 24;
set of int: WorkTime = 0..max(Time)*n_days;
set of int: Preference = exclusion..max([student_prefers[s,g] | s in Student, g in Group]);
set of int: GroupCohabitats = 1..length(group_cohabitats);

array[Student] of 0..5: student_break_importance;
array[Student, Group] of int: student_prefers;

array[Class] of Time: class_duration;
array[Class] of int: class_size;

array[Group] of Class: group_class;
array[Group] of Time: group_start;
array[Group] of Location: group_location;
array[Group] of Day: group_day;
array[int] of set of Group: group_cohabitats;

array[Location, Location] of Time: travel_duration;

% helper function
function var int: ceil_div(var int: x, var int: y) =
  x div y + ((x mod y) > 0);

array[Student] of var 0..0 : preference_disappointment;
array[Student] of var 0..0: normalized_break_disappointment;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% array[Student, Class] of var 0..n_groups: GroupAssignment;
% constraint forall(S in Student, C in Class)(if forall(G in Group where group_class[G]=C)(student_prefers[S,G] == -1) then GroupAssignment[S,C] = 0 endif);
array[Student, Group] of var bool: GroupAssignmentB;
constraint forall(S in Student, G in Group)(if student_prefers[S,G]=-1 then GroupAssignmentB[S,G] = false endif);

% constraint forall(S in Student, C in Class)(GroupAssignment[S,C]=0 \/ group_class[GroupAssignment[S,C]]=C);

% include "alldifferent.mzn";
% constraint forall(S in Student)(if forall(C1, C2 in Class where C1!=C2)(not (GroupAssignment[S,C1]=0 /\ GroupAssignment[S,C2]=0))
%     then alldifferent(C in Class)(GroupAssignment[S,C])
%     endif);

%nakładaja sie czasowo
predicate overlap_in_time(var Group: G1, var Group: G2) = group_day[G1] = group_day[G2] /\
        not(group_start[G1]+class_duration[group_class[G1]]+travel_duration[group_location[G1],group_location[G2]]<=group_start[G2] \/ group_start[G1]>=group_start[G2]+class_duration[group_class[G2]]+travel_duration[group_location[G2],group_location[G1]]);
        
constraint forall(S in Student, C in Class)(if attends[S,C]
then exists(G in Group where group_class[G] = C)(GroupAssignmentB[S,G]=true) endif);

array[Student, Class] of var bool: attends;
constraint forall(S in Student, C in Class)(if not forall(G in Group where group_class[G] = C)(student_prefers[S,G]=-1)
then attends[S,C]=true else attends[S,C]=false endif);

% array[Group,Group] of var 0..1: cohabited;
% constraint forall(G1, G2 in Group)(if exists(GC in GroupCohabitats, GC1, GC2 in group_cohabitats[GC])(G1=GC1 /\ G2=GC2 \/ G1=GC2 /\ G2=GC1) then cohabited[G1,G2] = true /\ cohabited[G2,G1] = true else cohabited[G1,G2] = false /\ cohabited[G2,G1] = false endif);

constraint forall(S in Student, G1, G2 in Group where G1<G2 /\ GroupAssignmentB[S,G1] /\ GroupAssignmentB[S,G2])(
not overlap_in_time(G1, G2)
\/ exists(G in GroupCohabitats)({G1, G2}=group_cohabitats[G])
);

constraint forall(S in Student, G in Group where class_size[group_class[G]]=174)(if student_prefers[S,G]!=-1 then GroupAssignmentB[S,G]=true endif);

constraint forall(G in Group)(sum(S in Student)(GroupAssignmentB[S,G])<=class_size[group_class[G]]);
constraint forall(S in Student, C in Class)(sum(G in Group where group_class[G]=C)(GroupAssignmentB[S,G])<=1);

var 0..0 : objective;


solve 
      :: seq_search([
        int_search(GroupAssignmentB, first_fail, indomain_min),
        ])
        satisfy;

output 
    ["assignment = [" ++ join(",", ["{" ++ join(", ", [show(g) |  g in Group where fix(GroupAssignmentB[s,g])]) ++ "}" | s in Student]) ++ "];\n"]  
%     [show([if GroupAssignmentB[S,G] then G else 0 endif| S in Student, G in Group]) ++ "\n"] 
    ++ ["total_break_disappointment = " ++ show(sum([normalized_break_disappointment[S] | S in Student])) ++ ";\n"]
    ++ ["total_preference_disappointment = " ++ show(sum(preference_disappointment)) ++ ";\n"]
    ++ ["objective = " ++ show(objective) ++ ";\n"]
%     ++ [show(exists(G in GroupCohabitats)({4,1} = group_cohabitats[G]))]
%     ++ [show([show(exists(G in GroupCohabitats)({G1, G2}=group_cohabitats[G])) ++ show(S) ++ show(G1) ++ show(G2) | S in Student,  G1, G2 in Group where G1<G2 /\ GroupAssignmentB[S,G1] /\ GroupAssignmentB[S,G2]])]
    
    
