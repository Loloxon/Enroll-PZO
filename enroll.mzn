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
int: maxObjective = 10000;
%niezadowolenie z przydziału grup do zminimalizowania
array[Student] of var Preference : preference_disappointment = [sum([best_preferences[S,C] - got_preferences[S,C]| C in Class]) | S in Student];  

array[Student, Class] of Preference : best_preferences = array2d(Student, Class, 
    [max([if group_class[G] = C then student_prefers[S,G] else -1 endif | G in Group]) | S in Student, C in Class]);
    
array[Student, Class] of var Preference : got_preferences = array2d(Student, Class, 
    [if GroupAssignment[S,C] != 0 then student_prefers[S,GroupAssignment[S,C]] else -1 endif | S in Student, C in Class]);
% niezadowolenie z powodu przerw
array[Student] of var 0..end*n_days : break_disappointment = [sum([staying_at_uni[S,D] - length_of_lessons[S,D] | D in Day where staying_at_uni[S,D]>=0]) | S in Student];

array[Student] of var 0..24*n_days: normalized_break_disappointment =
[ceil_div(break_disappointment[S],n_time_units_in_hour)| S in Student];

array[Student, Day] of var 0..end : staying_at_uni = array2d(Student, Day, 
    [max(max([if GroupAssignment[S,C] != 0 /\ group_day[GroupAssignment[S,C]] == D
                                       then group_start[GroupAssignment[S,C]] + class_duration[C] 
                                       else 0 endif 
                        | C in Class])
     - min([if GroupAssignment[S,C] != 0 /\ group_day[GroupAssignment[S,C]] == D 
                                       then group_start[GroupAssignment[S,C]] 
                                       else n_time_units_in_hour * 24 endif 
                        | C in Class]),0) | S in Student, D in Day]);
%%%%%%%%%%%%%% weird error and slower
% array[Student, Day] of var 0..end : staying_at_uni = array2d(Student, Day, 
%     [max(
%     if forall(C in Class)(GroupAssignment[S,C] == 0 \/ group_day[GroupAssignment[S,C]] != D) 
%       then 0
%       else
%         if exists(C1, C2 in Class where C1!=C2)
%   ((GroupAssignment[S,C1] != 0 /\ group_day[GroupAssignment[S,C1]] == D) /\ (GroupAssignment[S,C2] != 0 /\ group_day[GroupAssignment[S,C2]] == D)) 
%           then max([group_start[GroupAssignment[S,C]] + class_duration[C] 
%                | C in Class where GroupAssignment[S,C] != 0 /\ group_day[GroupAssignment[S,C]] == D])
%                - min([group_start[GroupAssignment[S,C]] 
%                | C in Class where GroupAssignment[S,C] != 0 /\ group_day[GroupAssignment[S,C]] == D])
%           else sum([
%                 if GroupAssignment[S,C] != 0 /\ group_day[GroupAssignment[S,C]] == D 
%                   then group_start[GroupAssignment[S,C]] + class_duration[C] 
%                   else 0 
%                 endif | C in Class]) 
%                - sum([
%                 if GroupAssignment[S,C] != 0 /\ group_day[GroupAssignment[S,C]] == D 
%                   then group_start[GroupAssignment[S,C]] 
%                   else 0 
%                 endif | C in Class])
%         endif
%     endif, 0) | S in Student, D in Day]);

array[Student, Day] of var 0..end : length_of_lessons; 
array[Student, Class] of var 0..end : length_of_lessons2; 
%niezadowolenie z powodu spóźnień
% array[Student, Day] of var set of int: lessons;
array[Student, Class] of var 0..n_groups: GroupAssignment = array2d(Student, Class, 
[if forall(G in Group)(student_prefers[S,G] == -1 \/ group_class[G] != C) 
    then 0   
    else _ endif | S in Student, C in Class]);

constraint forall(S in Student, C in Class)(GroupAssignment[S,C]=0 \/ group_class[GroupAssignment[S,C]]=C);

include "alldifferent.mzn";
constraint forall(S in Student)(if forall(C1, C2 in Class where C1!=C2)(not (GroupAssignment[S,C1]=0 /\ GroupAssignment[S,C2]=0))
    then alldifferent(C in Class)(GroupAssignment[S,C])
    endif);
%%%%%%%%% tego juz nie ma
% array[Student] of var 0..end*n_days: late_disappointment = [sum(
%                                                           [if GroupAssignment[S,C1]!=0 /\ GroupAssignment[S,C2] !=0 /\ group_day[GroupAssignment[S,C1]] == group_day[GroupAssignment[S,C2]] /\
%                                   not xorall([GroupAssignment[S,C1] in group_cohabitats[G] /\ GroupAssignment[S,C2] in group_cohabitats[G] | G in GroupCohabitats])
%                                                           then 
%                                                             if group_start[GroupAssignment[S,C1]] < group_start[GroupAssignment[S,C2]]
%                                                             then 
%                                                               if student_can_teleport[S]
%                                                                 then max(group_start[GroupAssignment[S,C1]] + class_duration[C1] - group_start[GroupAssignment[S,C2]],0)
%                                                                 else max(group_start[GroupAssignment[S,C1]] + class_duration[C1] + travel_duration[GroupAssignment[S,C1],GroupAssignment[S,C2]] - group_start[GroupAssignment[S,C2]],0)
%                                                               endif
%                                                             else
%                                                               if student_can_teleport[S]
%                                                                 then max(group_start[GroupAssignment[S,C2]] + class_duration[C2] - group_start[GroupAssignment[S,C1]],0)
%                                                                 else max(group_start[GroupAssignment[S,C2]] + class_duration[C2] + travel_duration[GroupAssignment[S,C2],GroupAssignment[S,C1]] - group_start[GroupAssignment[S,C1]],0)
%                                                               endif
%                                                             endif
%                                                           else 0
%                                                           endif 
%                                                           | C1, C2 in Class where C1>C2]) | S in Student];
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% numery grup(w tym klas) dla danego studenta dla danego dnia dla danej godziny
%przydział grup dla przedmiotów do studentów

% constraints
% studenci przypisanie do grup
constraint forall(S in Student, C in Class)
  (if not forall(G in Group)(student_prefers[S,G] == -1 \/ group_class[G] != C)
    then group_class[GroupAssignment[S,C]] == C /\ student_prefers[S,GroupAssignment[S,C]] != -1 endif);


array[Group,Group] of var 0..1: cohabited;
% constraint forall(G in GroupCohabitats)(forall(G1, G2 in group_cohabitats[G])(cohabited[G1,G2]=true));
% constraint forall(G1, G2 in Group)(if exists(GC in GroupCohabitats, GC1, GC2 in group_cohabitats[GC])(G1=GC1 /\ G2=GC2) then cohabited[G1,G2]=1 else cohabited[G1,G2]=0 endif);
constraint forall(G1, G2 in Group)(if exists(GC in GroupCohabitats, GC1, GC2 in group_cohabitats[GC])(G1=GC1 /\ G2=GC2 \/ G1=GC2 /\ G2=GC1) then cohabited[G1,G2] = true /\ cohabited[G2,G1] = true else cohabited[G1,G2] = false /\ cohabited[G2,G1] = false endif);

% grupy rozłączne
constraint forall(S in Student, C1, C2 in Class where C1 != C2 /\
 GroupAssignment[S,C1]!=0 /\ GroupAssignment[S,C2]!=0)(
cohabited[GroupAssignment[S,C1],GroupAssignment[S,C2]]=1 \/
    not overlap_in_time(GroupAssignment[S,C1],GroupAssignment[S,C2])
    );
%     \/ exists(G in GroupCohabitats, GC1, GC2 in group_cohabitats[G])(GroupAssignment[S,C1]=GC1 /\ GroupAssignment[S,C2]=GC2));
%     ({GroupAssignment[S,C1], GroupAssignment[S,C2]} = group_cohabitats[G] \/
%      {GroupAssignment[S,C2], GroupAssignment[S,C1]} = group_cohabitats[G]));

% constraint forall(S in Student, C1, C2 in Class where C1 != C2 /\ GroupAssignment[S,C1]!=0 /\ GroupAssignment[S,C2]!=0 /\ overlap_in_time(GroupAssignment[S,C1],GroupAssignment[S,C2]))(exists(G in GroupCohabitats)
%     ({GroupAssignment[S,C1], GroupAssignment[S,C2]} = group_cohabitats[G] \/
%      {GroupAssignment[S,C2], GroupAssignment[S,C1]} = group_cohabitats[G]));

%%%old version
% constraint forall(S in Student, C1,C2 in Class where C1!=C2)
%   (if GroupAssignment[S,C1]!=0 /\ GroupAssignment[S,C2]!=0 /\ group_day[GroupAssignment[S,C1]] == group_day[GroupAssignment[S,C2]]
%  /\ not exists(G in GroupCohabitats)({GroupAssignment[S,C1], GroupAssignment[S,C2]} = group_cohabitats[G] \/ {GroupAssignment[S,C2], GroupAssignment[S,C1]} = group_cohabitats[G])
  
% %   not xorall([GroupAssignment[S,C1] in group_cohabitats[G] /\ GroupAssignment[S,C2] in group_cohabitats[G] | G in GroupCohabitats])
%     then group_start[GroupAssignment[S,C1]] + class_duration[C1] + travel_duration[GroupAssignment[S,C1],GroupAssignment[S,C2]] <= group_start[GroupAssignment[S,C2]] \/
%           group_start[GroupAssignment[S,C2]] + class_duration[C2] + travel_duration[GroupAssignment[S,C2],GroupAssignment[S,C1]] <= group_start[GroupAssignment[S,C1]] 
%      endif);

%grupy nie przekraczaja liczebnosci
constraint forall(G in Group)(count(col(GroupAssignment,group_class[G]),G)<=class_size[group_class[G]]);


%%PREFERENCE_DISAPPOINTMENT
% liczenie oczekiwanych preferecnji na każdy przedmiot
% liczenie otrzymanych preferencji na każdy przedmiot
% liczenie sumy niezadowolenia z doboru grup

%liczenie niezadowolenia z przerw
%liczenie czasu na uniwesytecie razem z przerwami

% liczenie czasu na zajęciach
predicate overlap_in_time(var Group: G1, var Group: G2) = group_day[G1] = group_day[G2] /\
        group_start[G1]+class_duration[group_class[G1]]>group_start[G2] /\ group_start[G1]<group_start[G2]+class_duration[group_class[G2]];

array[Student, Class, Class] of var bool: coexists;
constraint forall(S in Student, C1, C2 in Class)(
    if C1=C2 \/ GroupAssignment[S,C1]!=0 /\ GroupAssignment[S,C2]!=0 /\ overlap_in_time(GroupAssignment[S,C1],GroupAssignment[S,C2])
      then coexists[S,C1,C2]=true
      else coexists[S,C1,C2]=false
    endif);

array[Student, Class] of var 1..n_classes: counted = array2d(Student, Class, 
[count(C1 in Class)(coexists[S,C,C1]) | S in Student, C in Class]);
constraint forall(S in Student, C in Class)(counted[S,C] = count(C1 in Class)(coexists[S,C,C1]=true));
% constraint forall(S in Student, C1, C2 in Class where C1!=C2 /\ GroupAssignment[S,C1]!=0 /\ GroupAssignment[S,C2]!=0 /\ overlap_in_time(GroupAssignment[S,C1],GroupAssignment[S,C2]))(
%     length_of_lessons[S,group_day[GroupAssignment[S,C1]]]=
%           ceil_div(
%           max([group_start[GroupAssignment[S,C1]]+class_duration[C1] |C1 in Class where GroupAssignment[S,C1]!=0 /\ coexists[S,C1,C2]]) - 
%           min([group_start[GroupAssignment[S,C1]] |C1 in Class where GroupAssignment[S,C1]!=0 /\ coexists[S,C1,C2]]),
%           counted[S,C1])
% );

% constraint forall(S in Student, D in Day)(length_of_lessons[S,D] = 
%   sum(
%     ['div'(max([group_start[GroupAssignment[S,C1]]+class_duration[C1] 
%          |C1 in Class where GroupAssignment[S,C1]!=0 /\ coexists[S,C,C1]]) - 
%      min([group_start[GroupAssignment[S,C1]]
%          |C1 in Class where GroupAssignment[S,C1]!=0 /\ coexists[S,C,C1]]),counted[S,C])
%      |C in Class where GroupAssignment[S,C]!=0 /\ group_day[GroupAssignment[S,C]]=D])
% );

constraint forall(S in Student, C in Class)(length_of_lessons2[S,C] = 
    if exists(C1 in Class where C1!=C)(coexists[S,C,C1])=false 
      then if GroupAssignment[S,C] = 0
              then 0
              else class_duration[C] 
            endif
      else 'div'(
           max([
%            lin_if(GroupAssignment[S,C1], 0)
           if GroupAssignment[S,C1]!=0 
                 then group_start[GroupAssignment[S,C1]]+class_duration[C1] 
                 else 0
                endif
                | C1 in Class where coexists[S,C,C1]=true] ++ [0]) - 
           min([if GroupAssignment[S,C1]!=0 
                 then group_start[GroupAssignment[S,C1]] 
                 else end 
                endif| C1 in Class where coexists[S,C,C1]=true] ++ [end]),
           counted[S,C])
    endif);

% constraint forall(S in Student, G in Group)(if GroupAssignment[S,group_class[G]]=G then GroupAssignmentB[S,G]=1 else GroupAssignmentB[S,G]=0 endif);
% constraint forall(S in Student, G in Group)(GroupAssignment[S,group_class[G]] >= G + 1 - M * delta20 - M * GroupAssignmentB[S,G] /\ GroupAssignment[S,group_class[G]] <= G - 1 + M * (1-delta20) + M * GroupAssignmentB[S,G]);
% a >= b + 1 - M δ - M c
% a <= b - 1 + M (1-δ) + M c
function var int: lin_if(var int:a, var int:b) = 
    let{
    var 0..1: c;
    var 0..1: delta;
    constraint a >= b + 1 - M * delta - M * c;
    constraint a <= b - 1 + M * (1-delta) + M * c;
    } in c;
% function var int: ceil_div(var int: x, var int: y) =
%   x div y + ((x mod y) > 0);
% function var int: lin_max(var set of int: Size, array[int] of var int: tab) = 
%   let{var int: x;
%       var 0..1: y;
%       constraint forall(S in Size)()
%       𝑥2−𝑥1≤𝑀𝑦
%       𝑥1−𝑥2≤𝑀(1−𝑦)
%       constraint forall(S in Size)(X<tab[S]);
%   } in x;

constraint forall(S in Student, D in Day)(length_of_lessons[S,D] = sum([if GroupAssignment[S,C]!=0 /\ group_day[GroupAssignment[S,C]]=D then length_of_lessons2[S,C] else 0 endif | C in Class]));

%liczenie break_dissapointment
%liczenie late_disappointment
%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%% old one
% var 0..maxObjective : objective = sum([pow(preference_disappointment[S] + break_to_disappointment_multiplier*break_disappointment[S] + late_to_disappointment_multiplier*late_disappointment[S],2) | S in Student]);
var 0..maxObjective : objective = sum([pow(ceil_div(student_break_importance[S] * normalized_break_disappointment[S] + (10 - student_break_importance[S]) * preference_disappointment[S],10),2) | S in Student]);
% var 0..MAX : objective = sum(preference_disappointment) + break_to_disappointment_multiplier*sum(break_disappointment)
%                         + late_to_disappointment_multiplier*sum(late_disappointment);
% solve minimize objective;
% solve :: int_search(preference_disappointment, smallest, indomain_min) minimize objective;
% solve :: int_search(GroupAssignment, first_fail, indomain_random) minimize objective;
% solve :: int_search(preference_disappointment, smallest, indomain_min) satisfy;
% solve :: int_search(preference_disappointment, smallest, indomain_min) satisfy;
% solve :: int_search(preference_disappointment, smallest, indomain_min) satisfy;
% solve :: int_search(GroupAssignment, first_fail, indomain_min) satisfy;
% solve :: seq_search([
%              int_search(s, smallest, indomain_min),
%              int_search([end], input_order, indomain_min)])
%       minimize end;
solve 
      :: seq_search([
        int_search(GroupAssignment, dom_w_deg, indomain_random),
%         int_search(got_preferences, dom_w_deg, indomain_random),
%         int_search(preference_disappointment, dom_w_deg, indomain_random),
%         int_search(break_disappointment, dom_w_deg, indomain_random),
        ])
%         satisfy;
        minimize objective;
        
% solve satisfy;

% najpierw numer studenta
% nastepnie dla kazdego studenta kolejne dni rozpisane na godziny
int: M = 100000;
var 0..1: delta20;
array[Student, Group] of var bool: GroupAssignmentB;
% array[Student, Group] of var 0..1: GroupAssignmentB2;
% constraint forall(S in Student, G in Group)(if GroupAssignmentB2[S,G]=1 then GroupAssignmentB[S,G]=true else GroupAssignmentB[S,G]=false endif);
% constraint forall(S in Student, G in Group)(if GroupAssignment[S,group_class[G]]=G then GroupAssignmentB[S,G]=1 else GroupAssignmentB[S,G]=0 endif);
constraint forall(S in Student, G in Group)(GroupAssignment[S,group_class[G]]=G /\ GroupAssignmentB[S,G] \/ GroupAssignment[S,group_class[G]]!=G /\ not GroupAssignmentB[S,G]);
% constraint forall(S in Student, G in Group)(GroupAssignment[S,group_class[G]] >= G + 1 - M * delta20 - M * GroupAssignmentB2[S,G] /\ GroupAssignment[S,group_class[G]] <= G - 1 + M * (1-delta20) + M * GroupAssignmentB2[S,G]);

% a >= b + 1 - M δ - M c
% a <= b - 1 + M (1-δ) + M c


output 
%       [show([show([coexists[S,C1,C2] | C1, C2 in Class]) | S in Student]) ++ "\n"] ++ 
%       [show([show([length_of_lessons2[S,C] | C in Class]) | S in Student]) ++ "\n"] ++
%       [show([counted[S,C] | S in Student, C in Class]) ++ "\n"] ++ 
%       [show([if GroupAssignment[S,group_class[G]]=G then GroupAssignment[S,group_class[G]] else 0 endif | S in Student, G in Group]) ++ "\n"] ++
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
++ [show(sum([true, true, true, false]))]
    









