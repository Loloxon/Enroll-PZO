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
int: being_late_treshold;
%% mnożymy ilość minut razy late_to_disappointment_multiplier 
int: late_to_disappointment_multiplier;
%% przerwa w minutach razy break_to_disappointment_multiplier 
int: break_to_disappointment_multiplier;

%sety zrobione z wartości wyżej
set of int: Student = 1..n_students;
set of int: Class = 1..n_classes;
set of int: Group = 1..n_groups;
set of int: Day = 1..n_days;
set of int: Location = 1..n_locations;
set of int: Time = 0..n_time_units_in_hour * 24;


set of int: Preference = exclusion..max([student_prefers[s,g] | s in Student, g in Group]);

%info o studentach
array[Student] of bool: student_can_teleport;
array[Student] of bool: student_loves_breaks;
array[Student, Group] of int: student_prefers;

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
int: MAX = 1000;

%niezadowolenie z przydziału grup do zminimalizowania
array[Student] of var Preference : preference_disappointment = [sum([best_preferences[S,C] - got_preferences[S,C]| C in Class]) | S in Student];  
array[Student, Class] of var Preference : best_preferences = array2d(Student, Class, [max([if group_class[G] = C then student_prefers[S,G] else -1 endif | G in Group]) | S in Student, C in Class]);
array[Student, Class] of var Preference : got_preferences = array2d(Student, Class, [if GroupAssignment[S,C] != 0 then student_prefers[S,GroupAssignment[S,C]] else -1 endif | S in Student, C in Class]);
%niezadowolenie z powodu przerw
array[Student] of var 0..n_time_units_in_hour * 24 * n_days : break_disappointment = [sum([staying_at_uni[S,D] - length_of_lessons[S,D] | D in Day where staying_at_uni[S,D]>=0]) | S in Student];
array[Student, Day] of var 0..n_time_units_in_hour * 24 : staying_at_uni = array2d(Student, Day, [max(max([if GroupAssignment[S,C] != 0 /\ group_day[GroupAssignment[S,C]] == D
                                                                      then group_start[GroupAssignment[S,C]] + class_duration[C] 
                                                                      else 0 endif 
                                                                      | C in Class])
                                                               - min([if GroupAssignment[S,C] != 0 /\ group_day[GroupAssignment[S,C]] == D 
                                                                       then group_start[GroupAssignment[S,C]] 
                                                                       else n_time_units_in_hour * 24 endif 
                                                                       | C in Class]),0) | S in Student, D in Day]);
array[Student, Day] of var 0..n_time_units_in_hour * 24 : length_of_lessons; 
array[Student, Class] of var 0..n_time_units_in_hour * 24 : length_of_lessons2; 
%niezadowolenie z powodu spóźnień
% array[Student, Day] of var set of int: lessons;
array[Student] of var 0..n_time_units_in_hour * 24: late_disappointment = [sum(
                                                          [if group_day[GroupAssignment[S,C1]] == group_day[GroupAssignment[S,C2]] /\
                                  not xorall([GroupAssignment[S,C1] in group_cohabitats[G] /\ GroupAssignment[S,C2] in group_cohabitats[G] | G in GroupCohabitats])
                                                          then 
                                                            if group_start[GroupAssignment[S,C1]] < group_start[GroupAssignment[S,C2]]
                                                            then 
                                                              if student_can_teleport[S]
                                                                then max(group_start[GroupAssignment[S,C1]] + class_duration[C1] - group_start[GroupAssignment[S,C2]],0)
                                                                else max(group_start[GroupAssignment[S,C1]] + class_duration[C1] + travel_duration[GroupAssignment[S,C1],GroupAssignment[S,C2]] - group_start[GroupAssignment[S,C2]],0)
                                                              endif
                                                            else
                                                              if student_can_teleport[S]
                                                                then max(group_start[GroupAssignment[S,C2]] + class_duration[C2] - group_start[GroupAssignment[S,C1]],0)
                                                                else max(group_start[GroupAssignment[S,C2]] + class_duration[C2] + travel_duration[GroupAssignment[S,C2],GroupAssignment[S,C1]] - group_start[GroupAssignment[S,C1]],0)
                                                              endif
                                                            endif
                                                          else 0
                                                          endif 
                                                          | C1, C2 in Class where C1>C2]) | S in Student];
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% numery grup(w tym klas) dla danego studenta dla danego dnia dla danej godziny
% array[Student, Day, start..end, 1..2] of var 0..n_groups: Schedule; 
%przydział grup dla przedmiotów do studentów
array[Student, Class] of var 0..n_groups: GroupAssignment;

% constraints
% studenci przypisanie do grup
constraint forall(S in Student, C in Class)
  (if forall(G in Group)(student_prefers[S,G] == -1 \/ group_class[G] != C) 
    then GroupAssignment[S,C] = 0   
    else group_class[GroupAssignment[S,C]] == C /\ student_prefers[S,GroupAssignment[S,C]] != -1 endif);  
    
% constraint forall(S in Student, C in Class)
%   (if sum([if student_prefers[S,G] == -1 \/ group_class[G] != C then 0 else 1 endif | G in Group]) < 1
%     then GroupAssignment[S,C] = 0   
%     else group_class[GroupAssignment[S,C]] == C /\ student_prefers[S,GroupAssignment[S,C]] != -1 endif);



% grupy rozłączne
constraint forall(S in Student, C1,C2 in Class where C1!=C2)
  (if group_day[GroupAssignment[S,C1]] == group_day[GroupAssignment[S,C2]] /\ not xorall([GroupAssignment[S,C1] in group_cohabitats[G] /\ GroupAssignment[S,C2] in group_cohabitats[G] | G in GroupCohabitats])
    then if student_can_teleport[S] 
      then group_start[GroupAssignment[S,C1]] + class_duration[C1] - being_late_treshold <= group_start[GroupAssignment[S,C2]] \/
          group_start[GroupAssignment[S,C2]] + class_duration[C2] - being_late_treshold <= group_start[GroupAssignment[S,C1]] 
      else group_start[GroupAssignment[S,C1]] + class_duration[C1] + travel_duration[GroupAssignment[S,C1],GroupAssignment[S,C2]] - being_late_treshold <= group_start[GroupAssignment[S,C2]] \/
          group_start[GroupAssignment[S,C2]] + class_duration[C2] + travel_duration[GroupAssignment[S,C2],GroupAssignment[S,C1]] - being_late_treshold <= group_start[GroupAssignment[S,C1]] 
     endif endif);

%grupy nie przekraczaja liczebnosci
constraint forall(G in Group)(count(col(GroupAssignment,group_class[G]),G)<=class_size[group_class[G]]);


%%PREFERENCE_DISAPPOINTMENT
% liczenie oczekiwanych preferecnji na każdy przedmiot
% constraint forall(S in Student, C in Class)(best_preferences[S,C] = max([if group_class[G] = C then student_prefers[S,G] else -1 endif | G in Group]));
% liczenie otrzymanych preferencji na każdy przedmiot
% constraint forall(S in Student, C in Class)(if GroupAssignment[S,C] != 0 then got_preferences[S,C] = student_prefers[S,GroupAssignment[S,C]] else got_preferences[S,C] = -1 endif);
%liczenie sumy niezadowolenia z doboru grup
% constraint forall(S in Student)(preference_disappointment[S] = sum([best_preferences[S,C] - got_preferences[S,C]| C in Class]));

%liczenie niezadowolenia z przerw
%liczenie czasu na uniwesytecie razem z przerwami
% constraint forall(S in Student, D in Day)(staying_at_uni[S,D] = max(max([if group_day[GroupAssignment[S,C]] == D 
%                                                                       then group_start[GroupAssignment[S,C]] + class_duration[C] 
%                                                                       else 0 endif 
%                                                                       | C in Class])
%                                                                - min([if group_day[GroupAssignment[S,C]] == D 
%                                                                        then group_start[GroupAssignment[S,C]] 
%                                                                        else n_time_units_in_hour * 24 endif 
%                                                                        | C in Class]),0));
% liczenie czasu na zajęciach
% predicate overlap_in_time(var Group: G1, var Group: G2) = if group_day[G1] = group_day[G2] 
%         then if group_start[G1]+class_duration[group_class[G1]]>group_start[G2] /\ group_start[G1]<group_start[G2]+class_duration[group_class[G2]]
%              then true
%              else false
%            endif
%         else false
%       endif;

% array[Student, Class, Class] of var bool: coexists;
% constraint forall(S in Student, C1, C2 in Class where GroupAssignment[S,C1]!=0 /\ GroupAssignment[S,C2]!=0)(
%     if overlap_in_time(GroupAssignment[S,C1],GroupAssignment[S,C2]) 
%       then coexists[S,C1,C2]=true
%       else coexists[S,C1,C2]=false
%     endif);

% array[Student, Class] of var 0..n_classes: counted;
% constraint forall(S in Student, C in Class)(counted[S,C] = count(C1 in Class)(coexists[S,C,C1]=true));
% constraint forall(S in Student, C in Class)(length_of_lessons2[S,C] = 
%     if forall(C1 in Class where C1!=C)(coexists[S,C,C1]=false) 
%       then if GroupAssignment[S,C] = 0
%               then 0
%               else class_duration[C] 
%             endif
%       else 'div'(max([group_start[GroupAssignment[S,C1]]+class_duration[C1] | C1 in Class where coexists[S,C,C1]=true]) - 
%            min([group_start[GroupAssignment[S,C1]] | C1 in Class where coexists[S,C,C1]=true]),counted[S,C]) 
% %            / count(C1 in Class)(coexists[S,C,C1]=true)
% %             /2
% %             /counted[S,C]
%     endif);
% constraint forall(S in Student, D in Day)(length_of_lessons[S,D] = sum([length_of_lessons2[S,C] | C in Class where group_day[GroupAssignment[S,C]]=D]));

% constraint forall(S in Student, D in Day)(length_of_lessons[S,D] = sum([if group_day[GroupAssignment[S,C]] == D 
%                                                                          then class_duration[C] 
%                                                                          else 0 endif 
%                                                                          | C in Class]));
%liczenie break_dissapointment
% constraint forall(S in Student)(break_disappointment[S] = sum([staying_at_uni[S,D] - length_of_lessons[S,D] | D in Day where staying_at_uni[S,D]>=0]));
%liczenie late_disappointment
% constraint forall(S in Student, D in Day)(if group_day[GroupAssignment[S,C]==D then lessons[S,D] endif| C in Class);
% constraint forall(S in Student)(late_disappointment[S] = sum(
%                                                           [if group_day[GroupAssignment[S,C1]] == group_day[GroupAssignment[S,C2]] /\
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
%                                                           | C1, C2 in Class where C1>C2]));

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%do wyświetlania
% constraint forall(S in Student, C1,C2 in Class where C1<C2)(
%         if not xorall([GroupAssignment[S,C1] in group_cohabitats[G] /\ GroupAssignment[S,C2] in group_cohabitats[G] | G in GroupCohabitats])
%         then
%         forall(T1 in start..end, T2 in start..end)
%               (if T1 >= group_start[GroupAssignment[S,C1]] /\ T1 < group_start[GroupAssignment[S,C1]] + class_duration[C1]-1 
%                   then Schedule[S,group_day[GroupAssignment[S,C1]],T1,1] = GroupAssignment[S,C1] /\
%                   Schedule[S,group_day[GroupAssignment[S,C1]],T1,2] = GroupAssignment[S,C1]
%                endif /\
%                if T2 >= group_start[GroupAssignment[S,C2]] /\ T2 < group_start[GroupAssignment[S,C2]] + class_duration[C2]-1
%                   then Schedule[S,group_day[GroupAssignment[S,C2]],T2,1] = GroupAssignment[S,C2] /\
%                   Schedule[S,group_day[GroupAssignment[S,C2]],T2,2] = GroupAssignment[S,C2] 
%                endif)
%         else
%         forall(T1 in start..end, T2 in start..end)
%               (if T1 >= group_start[GroupAssignment[S,C1]] /\ T1 < group_start[GroupAssignment[S,C1]] + class_duration[C1]-1 
%                   then Schedule[S,group_day[GroupAssignment[S,C1]],T1,1] = GroupAssignment[S,C1] 
%                endif /\
%                if T2 >= group_start[GroupAssignment[S,C2]] /\ T2 < group_start[GroupAssignment[S,C2]] + class_duration[C2]-1
%                   then Schedule[S,group_day[GroupAssignment[S,C2]],T2,2] = GroupAssignment[S,C2] 
%                endif)
%         endif);
     
%%%%%%%%%%%%%%%%%%%%%%%%%%
var 0..MAX : objective = sum([(preference_disappointment[S] + break_to_disappointment_multiplier*break_disappointment[S] + late_to_disappointment_multiplier*late_disappointment[S])*(preference_disappointment[S] + break_to_disappointment_multiplier*break_disappointment[S] + late_to_disappointment_multiplier*late_disappointment[S]) | S in Student]);
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
solve :: seq_search([
        int_search(GroupAssignment, dom_w_deg, indomain_random),
        int_search(got_preferences, dom_w_deg, indomain_random),
        int_search(preference_disappointment, dom_w_deg, indomain_random),
        int_search(break_disappointment, dom_w_deg, indomain_random),
        int_search(late_disappointment, dom_w_deg, indomain_random)
        ])
%         satisfy;
        minimize objective;
        
% solve satisfy;


% najpierw numer studenta
% nastepnie dla kazdego studenta kolejne dni rozpisane na godziny
array[Student, Group] of var bool: GroupAssignmentB;
constraint forall(S in Student, G in Group)(if GroupAssignment[S,group_class[G]]=G then GroupAssignmentB[S,G]=1 else GroupAssignmentB[S,G]=0 endif);
output 
%       [show([show([coexists[S,C1,C2] | C1, C2 in Class]) | S in Student]) ++ "\n"] ++ 
%       [show([show([length_of_lessons2[S,C] | C in Class]) | S in Student]) ++ "\n"] ++
%       [show([counted[S,C] | S in Student, C in Class]) ++ "\n"] ++ 
      ["assignment = [" ++ join(",", ["{" ++ join(", ", [show(g) |  g in Group where fix(GroupAssignmentB[s,g])]) ++ "}" | s in Student]) ++ "];\n"]
%     ++ ["being late table: " ++ show([late_disappointment[S] | S in Student]) ++ "\n"] 
    ++ ["total_late_disappointment = " ++ show(sum([late_disappointment[S] | S in Student])) ++ ";\n"]
%     ++ ["time spent at univer: " ++ show([staying_at_uni[S,C] | S in Student, C in Class]) ++ "\n"]
%     ++ ["length of lessons:    " ++ show([length_of_lessons[S,C] | S in Student, C in Class]) ++ "\n"]     
    ++ ["total_break_disappointment = " ++ show(sum([break_disappointment[S] | S in Student])) ++ ";\n"]
%     ++ ["best possible preferences: " ++ show([best_preferences[S,C] | S in Student, C in Class]) ++ "\n"] 
%     ++ ["preferences which got:     " ++ show([got_preferences[S,C] | S in Student, C in Class]) ++ "\n"]
    ++ ["total_preference_disappointment = " ++ show(sum(preference_disappointment)) ++ ";\n"]
    ++ ["objective = " ++ show(objective) ++ ";\n"]
    









