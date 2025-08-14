from z3 import *

# Define the days and times
days = ['Monday', 'Tuesday', 'Wednesday']
times = [(hour, minute) for hour in range(9, 17) for minute in [0, 30]]

# Create a dictionary to map each time slot to a Z3 Bool variable
time_vars = {(day, hour, minute): Bool(f"{day}_{hour:02d}{minute:02d}") for day in days for hour, minute in times}

# Define the constraints for Stephanie's schedule
stephanie_constraints = [
    Not(time_vars['Monday', 9, 30]), Not(time_vars['Monday', 10, 0]),
    Not(time_vars['Monday', 10, 30]), Not(time_vars['Monday', 11, 0]),
    Not(time_vars['Monday', 11, 30]), Not(time_vars['Monday', 12, 0]),
    Not(time_vars['Monday', 14, 0]), Not(time_vars['Monday', 14, 30]),
    Not(time_vars['Tuesday', 12, 0]), Not(time_vars['Tuesday', 13, 0]),
    Not(time_vars['Wednesday', 9, 0]), Not(time_vars['Wednesday', 10, 0]),
    Not(time_vars['Wednesday', 13, 0]), Not(time_vars['Wednesday', 14, 0])
]

# Define the constraints for Betty's schedule
betty_constraints = [
    Not(time_vars['Monday', 9, 0]), Not(time_vars['Monday', 10, 0]),
    Not(time_vars['Monday', 11, 0]), Not(time_vars['Monday', 11, 30]),
    Not(time_vars['Monday', 14, 30]), Not(time_vars['Monday', 15, 0]),
    Not(time_vars['Monday', 15, 30]), Not(time_vars['Monday', 16, 0]),
    Not(time_vars['Tuesday', 9, 0]), Not(time_vars['Tuesday', 9, 30]),
    Not(time_vars['Tuesday', 11, 30]), Not(time_vars['Tuesday', 12, 0]),
    Not(time_vars['Tuesday', 12, 30]), Not(time_vars['Tuesday', 14, 0]),
    Not(time_vars['Tuesday', 14, 30]), Not(time_vars['Tuesday', 15, 0]),
    Not(time_vars['Tuesday', 15, 30]), Not(time_vars['Tuesday', 16, 0]),
    Not(time_vars['Wednesday', 10, 0]), Not(time_vars['Wednesday', 11, 0]),
    Not(time_vars['Wednesday', 11, 30]), Not(time_vars['Wednesday', 12, 0]),
    Not(time_vars['Wednesday', 14, 0]), Not(time_vars['Wednesday', 14, 30]),
    Not(time_vars['Wednesday', 17, 0])
]

# Add the preference constraint for Stephanie (avoid Monday)
stephanie_avoid_monday = [Not(time_vars['Monday', hour, minute]) for hour, minute in times]

# Add the constraint for Betty (cannot meet on Tuesday after 12:30)
betty_tuesday_constraint = [Not(time_vars['Tuesday', hour, minute]) for hour, minute in times if hour > 12 or (hour == 12 and minute > 30)]

# Define the meeting duration constraint (1 hour)
meeting_duration = 2  # Since we have 30-minute intervals, 1 hour is 2 intervals

# Create a list to store the possible meeting slots
possible_slots = []

# Iterate over all possible start times and add constraints for meeting slots
for day in days:
    for hour, minute in times:
        start_time = (hour, minute)
        end_time = (hour + (minute + 30) // 60, (minute + 30) % 60) if minute == 30 else (hour + 1, 0)
        if end_time[0] < 17:  # Ensure the meeting ends before 17:00
            slot_vars = [time_vars[day, h, m] for h, m in [(start_time[0], start_time[1]), (end_time[0], end_time[1])]]
            possible_slots.append(And(*slot_vars))

# Combine all constraints
constraints = stephanie_constraints + betty_constraints + stephanie_avoid_monday + betty_tuesday_constraint + [Or(*possible_slots)]

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    for day in days:
        for hour, minute in times:
            start_time = (hour, minute)
            end_time = (hour + (minute + 30) // 60, (minute + 30) % 60) if minute == 30 else (hour + 1, 0)
            if end_time[0] < 17:  # Ensure the meeting ends before 17:00
                if model.evaluate(time_vars[day, start_time[0], start_time[1]]) and model.evaluate(time_vars[day, end_time[0], end_time[1]]):
                    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time[0]:02d}:{start_time[1]:02d}\nEnd Time: {end_time[0]:02d}:{end_time[1]:02d}")
                    break
else:
    print("No solution found")