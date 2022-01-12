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

%niezadowolenie z przydziału grup do zminimalizowania
array[Student] of var Preference : preference_disappointment;  
array[Student, Class] of var Preference : best_preferences;
array[Student, Class] of var Preference : got_preferences;
%niezadowolenie z powodu przerw
array[Student] of var int : break_disappointment;
array[Student, Day] of var int : staying_at_uni;
array[Student, Day] of var int : length_of_lessons; 
%niezadowolenie z powodu spóźnień
% array[Student, Day] of var set of int: lessons;
array[Student] of var int: late_disappointment;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% numery grup(w tym klas) dla danego studenta dla danego dnia dla danej godziny
array[Student, Day, start..end, 1..2] of var 0..n_groups: Schedule; 
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
constraint forall(S in Student, C in Class)(best_preferences[S,C] = max([if group_class[G] = C then student_prefers[S,G] else -1 endif | G in Group]));
% liczenie otrzymanych preferencji na każdy przedmiot
constraint forall(S in Student, C in Class)(if GroupAssignment[S,C] != 0 then got_preferences[S,C] = student_prefers[S,GroupAssignment[S,C]] else got_preferences[S,C] = -1 endif);
%liczenie sumy niezadowolenia z doboru grup
constraint forall(S in Student)(preference_disappointment[S] = sum([best_preferences[S,C] - got_preferences[S,C]| C in Class]));

%liczenie niezadowolenia z przerw
%liczenie czasu na uniwesytecie razem z przerwami
constraint forall(S in Student, D in Day)(staying_at_uni[S,D] = max([if group_day[GroupAssignment[S,C]] == D 
                                                                      then group_start[GroupAssignment[S,C]] + class_duration[C] 
                                                                      else 0 endif 
                                                                      | C in Class])
                                                               - min([if group_day[GroupAssignment[S,C]] == D 
                                                                       then group_start[GroupAssignment[S,C]] 
                                                                       else n_time_units_in_hour * 24 endif 
                                                                       | C in Class]));
% liczenie czasu na zajęciach
constraint forall(S in Student, D in Day)(length_of_lessons[S,D] = sum([if group_day[GroupAssignment[S,C]] == D 
                                                                         then class_duration[C] 
                                                                         else 0 endif 
                                                                         | C in Class]));
%liczenie break_dissapointment
constraint forall(S in Student)(break_disappointment[S] = sum([staying_at_uni[S,D] - length_of_lessons[S,D] | D in Day where staying_at_uni[S,D]>=0]));
%liczenie late_disappointment
% constraint forall(S in Student, D in Day)(if group_day[GroupAssignment[S,C]==D then lessons[S,D] endif| C in Class);
constraint forall(S in Student)(late_disappointment[S] = sum(
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
                                                          | C1, C2 in Class where C1>C2]));

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
var 0..infinity : objective = sum(preference_disappointment) + sum([break_to_disappointment_multiplier*break_disappointment[S] | S in Student])
                        + sum([late_to_disappointment_multiplier*late_disappointment[S] | S in Student]);
% solve minimize objective;
solve :: int_search(preference_disappointment, first_fail, indomain_min) minimize objective;


% najpierw numer studenta
% nastepnie dla kazdego studenta kolejne dni rozpisane na godziny
 
output 
%     ["Time:"] ++ [if T<100 then " " ++ show(T) ++ ";" else show(T) ++ ";" endif |T in start..end] ++ ["\n"] ++
%     [if T==start then show(S) ++ "." else "" endif ++
%     if T==start then show(D) ++ ":  " else "" endif ++
%     show(Schedule[S,D,T,1]) ++ "" ++ show(Schedule[S,D,T,2]) ++ if T == end then "\n" else "; " endif ++ 
%     if T == end /\ D==n_days then "\n" else "" endif
%     |S in Student, 
%     D in Day, 
%     T in start..end] ++
    ["assignment = ["] ++ 
    [if C = 1 then "{" else " " endif ++ show(GroupAssignment[S,C]) ++ if C = n_classes then "}" else "" endif ++ 
    if C = n_classes /\ S = n_students then "" else "," endif | S in Student, C in Class]
    ++ ["];\ntotal_late_disappointment = " ++ show(sum([late_to_disappointment_multiplier*late_disappointment[S] | S in Student])) ++ ";\n"]
    ++ ["total_break_disappointment = " ++ show(sum([break_to_disappointment_multiplier*break_disappointment[S] | S in Student])) ++ ";\n"]
    ++ ["total_preference_disappointment = " ++ show(sum(preference_disappointment)) ++ ";\n"]
    ++ ["objective = " ++ show(objective) ++ ";\n"]
%     ++ ["bst pref: " ++ show([best_preferences[S,C] | S in Student, C in Class]) ++ "\n"] 
%     ++ ["got pref: " ++ show([got_preferences[S,C] | S in Student, C in Class]) ++ "\n"]
%     ++ ["pref dis: " ++ show(sum(preference_disappointment)) ++ "\n"]
%     ++ ["at uni  : " ++ show([staying_at_uni[S,C] | S in Student, C in Class]) ++ "\n"]
%     ++ ["length  : " ++ show([length_of_lessons[S,C] | S in Student, C in Class]) ++ "\n"] 
%     ++ ["break  s: " ++ show(sum([break_to_disappointment_multiplier*break_disappointment[S] | S in Student])) ++ "\n"]
% %     ++ [show([staying_at_uni[S,C] | S in Student, C in Class]) ++ "\n"]
%     ++ ["late tab: " ++ show([late_disappointment[S] | S in Student]) ++ "\n"] 
%     ++ ["late sum: " ++ show(sum([late_to_disappointment_multiplier*late_disappointment[S] | S in Student])) ++ "\n"]
%     ++ ["overall : " ++ show(objective) ++ "\n"]
    









