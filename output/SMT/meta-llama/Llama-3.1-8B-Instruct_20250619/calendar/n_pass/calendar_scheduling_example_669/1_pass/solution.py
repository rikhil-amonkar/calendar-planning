from z3 import *

# Define the variables
day = IntSort()
start_time = IntSort()
end_time = IntSort()

# Define the constraints
monday = 1
tuesday = 2
meeting_duration = 30

# Define the schedules for Jean and Doris
jean_monday = [IntVectorSort(2), [9, 17]]
jean_tuesday = [IntVectorSort(2), [9, 17]]

doris_monday = [IntVectorSort(5), [9, 11, 30, 16, 17]]
doris_tuesday = [IntVectorSort(5), [9, 17]]

# Define the constraints for Doris' preferences
doris_preference = [monday, 14]

# Define the meeting duration in minutes
meeting_duration_minutes = meeting_duration * 60

# Define the solver
solver = Solver()

# Define the day variable
day_var = Int('day')
solver.add(day_var == monday)
solver.add(day_var == tuesday)

# Define the start and end time variables
start_time_var = Int('start_time')
end_time_var = Int('end_time')

# Define the constraints for the start and end times
solver.add(9 * 60 <= start_time_var)
solver.add(start_time_var <= 17 * 60)
solver.add(start_time_var + meeting_duration_minutes <= 17 * 60)

# Define the constraints for Jean's schedule
jean_schedule = If(day_var == monday, jean_monday, jean_tuesday)
for i in range(len(jean_schedule)):
    solver.add(jean_schedule[i] * 60 <= start_time_var)
    solver.add(start_time_var + meeting_duration_minutes <= (jean_schedule[i] + 1) * 60)

# Define the constraints for Doris' schedule
doris_schedule = If(day_var == monday, doris_monday, doris_tuesday)
for i in range(len(doris_schedule)):
    if doris_schedule[i]!= 14:
        solver.add(doris_schedule[i] * 60 <= start_time_var)
        solver.add(start_time_var + meeting_duration_minutes <= (doris_schedule[i] + 1) * 60)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day_var]
    start_time_value = model[start_time_var]
    end_time_value = model[end_time_var]
    start_time_str = str(start_time_value // 60).zfill(2) + str(start_time_value % 60).zfill(2)
    end_time_str = str(end_time_value // 60).zfill(2) + str(end_time_value % 60).zfill(2)
    print('SOLUTION:')
    print(f'Day: {["Monday", "Tuesday"][day_value - 1]}')
    print(f'Start Time: {start_time_str}')
    print(f'End Time: {end_time_str}')
else:
    print('No solution found.')