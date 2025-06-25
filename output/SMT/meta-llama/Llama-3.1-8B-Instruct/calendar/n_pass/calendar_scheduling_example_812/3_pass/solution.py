YOUR_CODE
from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

# Define the start and end times
start_times = ['09:00', '09:30', '10:00', '10:30', '11:00', '11:30', '12:00', '12:30', '13:00', '13:30', '14:00', '14:30', '15:00', '15:30', '16:00', '16:30', '17:00']
end_times = ['09:30', '10:00', '10:30', '11:00', '11:30', '12:00', '12:30', '13:00', '13:30', '14:00', '14:30', '15:00', '15:30', '16:00', '16:30', '17:00', '17:30']

# Convert start and end times to minutes
start_times_minutes = [int(t[:2]) * 60 + int(t[3:]) for t in start_times]
end_times_minutes = [int(t[:2]) * 60 + int(t[3:]) for t in end_times]

# Define the meeting duration in minutes
meeting_duration = 30

# Define the existing schedules for Mary and Alexis
mary_schedule = {
    'Monday': [],
    'Tuesday': [start_times_minutes[2], start_times_minutes[13], start_times_minutes[14]],
    'Wednesday': [start_times_minutes[1], start_times_minutes[13]],
    'Thursday': [start_times_minutes[0], start_times_minutes[5]]
}

alexis_schedule = {
    'Monday': [start_times_minutes[0], start_times_minutes[2], start_times_minutes[8], start_times_minutes[14]],
    'Tuesday': [start_times_minutes[0], start_times_minutes[2], start_times_minutes[5], start_times_minutes[7], start_times_minutes[13], start_times_minutes[16]],
    'Wednesday': [start_times_minutes[0], start_times_minutes[2], start_times_minutes[11]],
    'Thursday': [start_times_minutes[4], start_times_minutes[10], start_times_minutes[13], start_times_minutes[14], start_times_minutes[16]]
}

# Define the solver
solver = Solver()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time = [Bool(f'start_time_{i}') for i in range(len(start_times))]
end_time = [Bool(f'end_time_{i}') for i in range(len(end_times))]

# Define the constraints
for i, d in enumerate(days):
    solver.add(Or([day[i]]))
    for t in mary_schedule[d]:
        if t in start_times_minutes:
            solver.add(Not(And([day[i], start_time[start_times_minutes.index(t)]])))
    for t in alexis_schedule[d]:
        if t in start_times_minutes:
            solver.add(Not(And([day[i], start_time[start_times_minutes.index(t)]])))
    solver.add(Implies(day[i], Or([start_time[t] for t in range(len(start_times))])))
    solver.add(Implies(day[i], Or([end_time[t] for t in range(len(end_times))])))
    solver.add(Implies(day[i], start_time[0] == Or([start_time[t] for t in range(1, len(start_times))])))
    solver.add(Implies(day[i], end_time[-1] == Or([end_time[t] for t in range(len(end_times) - 1)])))
    for t in range(len(start_times)):
        solver.add(Implies(day[i], And([start_time[t], end_time[t] == start_time[t] + meeting_duration])))
        solver.add(Implies(day[i], And([end_time[t], start_time[t] == end_time[t] - meeting_duration])))

# Check the solution
if solver.check() == sat:
    model = solver.model()
    day_index = [i for i, d in enumerate(days) if model.evaluate(day[i]).as_bool() == True][0]
    start_time_index = [i for i, t in enumerate(start_times) if model.evaluate(start_time[i]).as_bool() == True][0]
    end_time_index = [i for i, t in enumerate(end_times) if model.evaluate(end_time[i]).as_bool() == True][0]
    print(f"SOLUTION:")
    print(f"Day: {days[day_index]}")
    print(f"Start Time: {start_times[start_time_index]}")
    print(f"End Time: {end_times[end_time_index]}")
else:
    print("No solution exists.")