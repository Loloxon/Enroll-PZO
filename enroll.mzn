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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%time range
int: start = min(group_start);
int: end = max(group_start) + max(class_duration);

%niezadowolenie z przydziału grup do zminimalizowania
array[Student] of var Preference : preference_disappointment;  
array[Student, Class] of var Preference : best_preferences;
array[Student, Class] of var Preference : got_preferences;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% numery grup(w tym klas) dla danego studenta dla danego dnia dla danej godziny
array[Student, Day, start..end] of var 0..n_groups: Schedule; 
%przydział grup dla przedmiotów do studentów
array[Student, Class] of var 0..n_groups: GroupAssignment;

% constraints
%studenci przypisanie do grup
constraint forall(S in Student, C in Class)
  (if forall(G in Group)(student_prefers[S,G] == -1 \/ group_class[G] != C) 
    then GroupAssignment[S,C] = 0   
    else group_class[GroupAssignment[S,C]] = C /\ student_prefers[S,GroupAssignment[S,C]] != -1 endif);  


%grupy rozłączne
constraint forall(S in Student, C1,C2 in Class where C1<C2)
  (if group_day[GroupAssignment[S,C1]] == group_day[GroupAssignment[S,C2]]% oraz nie są cohabitats *TODO*
    then if student_can_teleport[S] 
      then group_start[GroupAssignment[S,C1]] + class_duration[C1] - being_late_treshold <= group_start[GroupAssignment[S,C2]]
      else group_start[GroupAssignment[S,C1]] + class_duration[C1] + travel_duration[GroupAssignment[S,C1],GroupAssignment[S,C2]] - being_late_treshold <= group_start[GroupAssignment[S,C2]] 
     endif endif);

%grupy nie przekraczaja liczebnosci
constraint forall(G in Group)(count(col(GroupAssignment,group_class[G]),G)<=class_size[group_class[G]]);

%liczenie sumy niezadowolenia z doboru grup
%liczenie najlepszych preferencji
constraint forall(S in Student, C in Class)(best_preferences[S,C] = max([if group_class[G] = C then student_prefers[S,G] else -1 endif | G in Group]));
%liczenie otrzymanych preferencji
constraint forall(S in Student, C in Class)(if GroupAssignment[S,C] != 0 then got_preferences[S,C] = student_prefers[S,GroupAssignment[S,C]] else got_preferences[S,C] = -1 endif);
%liczenie preference disappointment
constraint forall(S in Student)(preference_disappointment[S] = sum([best_preferences[S,C] - got_preferences[S,C]| C in Class]));

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%do wyświetlania
constraint forall(S in Student, D in Day, T in start..end, C in Class)
  (if group_day[GroupAssignment[S,C]] == D /\
     T >= group_start[GroupAssignment[S,C]] /\ 
     T < group_start[GroupAssignment[S,C]] + class_duration[C] then Schedule[S,D,T] = GroupAssignment[S,C] endif);
%%%%%%%%%%%%%%%%%%%%%%%%%%
solve minimize sum(preference_disappointment);

% najpierw numer studenta
% nastepnie dla kazdego studenta kolejne dni rozpisane na godziny
 
output ["Time:"] ++ [if T<100 then show(T) ++ ", " else show(T) ++ "," endif |T in start..end] ++ ["\n"] ++
    [if T==start then show(S) ++ "." else "" endif ++
    if T==start then show(D) ++ ": " else "" endif ++
    show(Schedule[S,D,T]) ++ if T == end then "\n" else ",  " endif ++ 
    if T == end /\ D==n_days then "\n" else "" endif
    |S in Student, 
    D in Day, 
    T in start..end]









