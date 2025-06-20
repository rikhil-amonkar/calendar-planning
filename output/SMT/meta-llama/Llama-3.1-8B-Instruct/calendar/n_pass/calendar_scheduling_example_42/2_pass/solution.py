from z3 import *

def schedule_meeting(julie_schedule, sean_schedule, lori_schedule, duration):
    # Define the day
    day = 'Monday'

    # Define the start and end times
    start_time = 9
    end_time = 17

    # Create a time grid
    time_grid = [[Bool(f"time_{day}_{i}_{j}") for j in range(start_time, end_time + 1)] for i in range(start_time, end_time + 1)]

    # Define the constraints
    s = Solver()
    for i in range(start_time, end_time + 1):
        for j in range(start_time, end_time + 1):
            # Conflict with Julie's schedule
            if [i, j] in julie_schedule:
                s.add(Not(time_grid[i][j]))
            # Conflict with Sean's schedule
            if [i, j] in sean_schedule:
                s.add(Not(time_grid[i][j]))
            # Conflict with Lori's schedule
            if [i, j] in lori_schedule:
                s.add(Not(time_grid[i][j]))

    # Meeting duration constraint
    for i in range(start_time, end_time + 1):
        for j in range(start_time, end_time - duration + 1):
            s.add(Implies(time_grid[i][j], Not(time_grid[i][j + duration])))

    # Find a valid time slot
    s.add(Or([time_grid[i][j] for i in range(start_time, end_time + 1) for j in range(start_time, end_time + 1 - duration)]))
    if s.check() == sat:
        model = s.model()
        for i in range(start_time, end_time + 1):
            for j in range(start_time, end_time + 1):
                if model.evaluate(time_grid[i][j]):
                    return f"SOLUTION:\nDay: {day}\nStart Time: {j:02d}:00\nEnd Time: {(j + duration):02d}:00"
    return "No valid time slot found"

# Example usage
julie_schedule = [[9, 30], [11, 30], [12, 30], [13, 30], [16, 0]]
sean_schedule = [[9, 30], [13, 0], [15, 30], [16, 30]]
lori_schedule = [[10, 30], [11, 30], [12, 30], [13, 0], [15, 30]]
duration = 1

print(schedule_meeting(julie_schedule, sean_schedule, lori_schedule, duration))