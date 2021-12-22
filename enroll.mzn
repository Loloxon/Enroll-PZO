% Parameters
int: n_students;
int: n_days;
int: n_classes;
int: n_groups;
int: n_locations;

int: n_time_units_in_hour;
int: exclusion = -1;

%% nieprzekraczalne 
int: being_late_treshold;
%% mnożymy ilość minut razy late_to_disappointment_multiplier 
int: late_to_disappointment_multiplier;
%% przerwa w minutach razy break_to_disappointment_multiplier 
int: break_to_disappointment_multiplier;

set of int: Student = 1..n_students;
set of int: Class = 1..n_classes;
set of int: Group = 1..n_groups;
set of int: Day = 1..n_days;
set of int: Location = 1..n_locations;
set of int: Time = 0..n_time_units_in_hour * 24;
set of int: Preference = exclusion..max([student_prefers[s,g] | s in Student, g in Group]);

array[Student] of bool: student_can_teleport;
array[Student] of bool: student_loves_breaks;
array[Student, Group] of int: student_prefers;

array[Class] of Time: class_duration;
array[Class] of int: class_size;

array[Group] of Class: group_class;
array[Group] of Time: group_start;
array[Group] of Location: group_location;
array[Group] of Day: group_day;
array[int] of set of Group: group_cohabitats;

array[Location, Location] of Time: travel_duration;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
int: start = min(group_start);
int: end = max(group_start) + max(class_duration);
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% numery klas dla danego studenta dla danego dnia
array[Student, Day, start..end] of var Group: Schedule; 

% constraint ;

solve satisfy;

% najpierw numer studenta
% nastepnie dla kazdego studenta kolejne dni rozpisane na godziny
 
output [if D==1 /\ T==start then "student nr: " ++ show(S) ++ ".\n" else "" endif ++
    if T==start then show(D) ++ ": " else "" endif ++
    show(Schedule[S,D,T]) ++ if T == end then "\n" else ", " endif
    |S in Student, 
    D in Day, 
    T in start..end]









