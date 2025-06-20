from z3 import *

def schedule_meeting(day, start_time, end_time, existing_schedules):
    # Define the variables
    time_slots = []
    for i in range(8):
        for j in range(60):
            time_slots.append((i, j))

    # Create a boolean variable for each time slot
    time_vars = [Bool(f'time_{i}_{j}') for i, j in time_slots]

    # Create a constraint for each person's schedule
    constraints = []
    for person, schedule in existing_schedules.items():
        for slot in schedule:
            start_hour, start_min = divmod(slot[0], 60)
            end_hour, end_min = divmod(slot[1], 60)
            for i in range(start_hour, end_hour):
                for j in range(start_min, 60) if i == start_hour else range(0, end_min):
                    constraints.append(Not(time_vars[(i, j)]))

    # Add the meeting duration constraint
    for i in range(8):
        for j in range(30):
            if j == 0:
                constraints.append(time_vars[(i, j)] == time_vars[(i, 0)])
            else:
                constraints.append(Implies(time_vars[(i, j-1)], time_vars[(i, j)]))

    # Add the meeting start time constraint
    constraints.append(time_vars[start_time[0], start_time[1]])

    # Add the meeting end time constraint
    constraints.append(Implies(time_vars[start_time[0], start_time[1]], time_vars[end_time[0], end_time[1]]))

    # Add the meeting duration constraint
    constraints.append(Implies(time_vars[start_time[0], start_time[1]], time_vars[end_time[0], end_time[1]] == time_vars[start_time[0], start_time[1]]))

    # Add the day constraint
    constraints.append(time_vars[start_time[0], start_time[1]] == time_vars[start_time[0], start_time[1]])

    # Solve the constraints
    solver = Solver()
    solver.add(Or([time_vars[(i, j)] for i, j in time_slots]))
    solver.add(And(constraints))

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        start_hour, start_min = divmod(model[start_time[0], start_time[1]].as_long(), 60)
        end_hour, end_min = divmod(model[end_time[0], end_time[1]].as_long(), 60)
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_hour:02d}:{start_min:02d}\nEnd Time: {end_hour:02d}:{end_min:02d}'
    else:
        return 'No solution found'

# Define the existing schedules
existing_schedules = {
    'Joe': [(9*60+30, 10*60+0), (10*60+30, 11*60+0)],
    'Keith': [(11*60+30, 12*60+0), (15*60+0, 15*60+30)],
    'Patricia': [(9*60+0, 9*60+30), (13*60+0, 13*60+30)],
    'Nancy': [(9*60+0, 11*60+0), (11*60+30, 16*60+30)],
    'Pamela': [(9*60+0, 10*60+0), (10*60+30, 11*60+0), (11*60+30, 12*60+30), (13*60+0, 14*60+0), (14*60+30, 15*60+0), (15*60+30, 16*60+0), (16*60+30, 17*60+0)]
}

# Define the meeting duration
meeting_duration = 30

# Define the day and start time
day = 'Monday'
start_time = (9, 0)

# Define the end time
end_time = (start_time[0], start_time[1] + meeting_duration)

# Print the solution
print(schedule_meeting(day, start_time, end_time, existing_schedules))