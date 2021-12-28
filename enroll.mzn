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
%nie wiem do czego to miało by być
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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% numery grup(w tym klas) dla danego studenta dla danego dnia dla danej godziny
array[Student, Day, start..end] of var 0..n_groups: Schedule; 
%przydział grup dla przedmiotów do studentów
array[Student, Class] of var 0..n_groups: GroupAssignment;

% constraints
constraint forall(S in Student, C in Class)
  (if forall(G in Group)(student_prefers[S,G] == -1 \/ group_class[G] != C) then GroupAssignment[S,C] = 0 else group_class[GroupAssignment[S,C]] = C endif);  

% constraint forall(S in Student, D in Day, T in start..end, id in Group)
%   (if T >= group_start[id] /\ T < group_start[id] + class_duration[group_class[id]] /\  D == group_day[id]
%   then Schedule[S,D,T] = S endif);

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%do wyświetlania
constraint forall(S in Student, D in Day, T in start..end, C in Class)
  (if group_day[GroupAssignment[S,C]] == D /\
     T >= group_start[GroupAssignment[S,C]] /\ 
     T < group_start[GroupAssignment[S,C]] + class_duration[C] then Schedule[S,D,T] = GroupAssignment[S,C] endif);
%%%%%%%%%%%%%%%%%%%%%%%%%%
solve satisfy;

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









