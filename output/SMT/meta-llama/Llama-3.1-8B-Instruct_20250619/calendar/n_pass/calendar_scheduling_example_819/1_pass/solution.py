from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

# Define the start and end times of the workday
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # half an hour

# Define the existing schedules for Ruth
ruth_schedule = {
    'Monday': [(start_time, end_time)],
    'Tuesday': [(start_time, end_time)],
    'Wednesday': [(start_time, end_time)],
    'Thursday': [(start_time, start_time + 90), (start_time + 120, end_time)]
}

# Define the constraints for Julie
julie_constraints = {
    'Thursday': [(start_time + 90, end_time)]  # Julie wants to avoid meetings before 11:30 on Thursday
}

# Define the solver
solver = Optimize()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time_var = [Int(f'start_time_{i}') for i in range(len(days))]
end_time_var = [Int(f'end_time_{i}') for i in range(len(days))]

# Define the constraints
for i, day_name in enumerate(days):
    solver.add(day[i])  # at least one day
    solver.add(Or([day[i] for i in range(len(days))]))  # exactly one day
    solver.add(start_time_var[i] >= start_time)
    solver.add(start_time_var[i] <= end_time - meeting_duration)
    solver.add(end_time_var[i] >= start_time_var[i] + meeting_duration)
    solver.add(end_time_var[i] <= end_time)
    
    # Ruth's schedule constraints
    for time in ruth_schedule[day_name]:
        solver.add(start_time_var[i] >= time[0])
        solver.add(start_time_var[i] <= time[1])
        solver.add(end_time_var[i] >= time[0])
        solver.add(end_time_var[i] <= time[1])
        
    # Julie's constraints
    if day_name == 'Thursday':
        for time in julie_constraints[day_name]:
            solver.add(start_time_var[i] >= time[0])
            solver.add(start_time_var[i] <= time[1])
            solver.add(end_time_var[i] >= time[0])
            solver.add(end_time_var[i] <= time[1])

# Solve the optimization problem
solution = solver.check()
if solution == sat:
    model = solver.model()
    day_to_meet = days[model[day[0]].as_bool().which()]
    start_time_to_meet = model[start_time_var[0]].as_int()
    end_time_to_meet = model[end_time_var[0]].as_int()
    
    print(f"SOLUTION:")
    print(f"Day: {day_to_meet}")
    print(f"Start Time: {start_time_to_meet // 60:02d}:{start_time_to_meet % 60:02d}")
    print(f"End Time: {(end_time_to_meet // 60):02d}:{(end_time_to_meet % 60):02d}")
else:
    print("No solution found.")