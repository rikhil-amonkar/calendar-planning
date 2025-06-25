YOUR_CODE
from z3 import *

# Define the variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
monday = 1
tuesday = 2
meeting_duration = 30

# Define the schedules for Jean and Doris
jean_monday = [9, 17]
jean_tuesday = [9, 17]

doris_monday = [9, 11, 30, 16, 17]
doris_tuesday = [9, 17]

# Define the constraints for Doris' preferences
doris_preference = [monday, 14]

# Define the meeting duration in minutes
meeting_duration_minutes = meeting_duration * 60

# Define the solver
solver = Solver()

# Define the constraints for the start and end times
for day_value in [monday, tuesday]:
    for start_time_value in range(9 * 60, 17 * 60):
        for end_time_value in range(start_time_value + meeting_duration_minutes, 17 * 60 + 1):
            day_var = day_value
            start_time_var = start_time_value
            end_time_var = end_time_value
            # Define the constraints for Jean's schedule
            jean_schedule = If(day_var == monday, jean_monday, jean_tuesday)
            for i in range(len(jean_schedule)):
                if jean_schedule[i] * 60 <= start_time_var and start_time_var + meeting_duration_minutes <= (jean_schedule[i] + 1) * 60:
                    break
            else:
                continue
            # Define the constraints for Doris' schedule
            doris_schedule = If(day_var == monday, doris_monday, doris_tuesday)
            for i in range(len(doris_schedule)):
                if doris_schedule[i]!= 14 and doris_schedule[i] * 60 <= start_time_var and start_time_var + meeting_duration_minutes <= (doris_schedule[i] + 1) * 60:
                    break
            else:
                continue
            # Solve the problem
            solver.push()
            solver.add(day_var == day_value)
            solver.add(start_time_var == start_time_value)
            solver.add(end_time_var == end_time_value)
            solver.add(9 * 60 <= start_time_var)
            solver.add(start_time_var <= 17 * 60)
            solver.add(start_time_var + meeting_duration_minutes <= 17 * 60)
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
                solver.pop()
                break
            solver.pop()
else:
    print('No solution found.')