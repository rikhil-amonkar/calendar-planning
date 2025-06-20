from z3 import *

def schedule_meeting(julie_schedule, sean_schedule, lori_schedule, duration):
    # Define the day
    day = 'Monday'

    # Define the start and end times
    start_time = [9, 30]  # Start at 9:30 to avoid conflicts with existing schedules
    end_time = 17

    # Create a time grid
    time_grid = [[Bool(f"time_{day}_{i}_{j}") for j in range(start_time[0], end_time + 1)] for i in range(start_time[1], 18)]

    # Define the constraints
    for i in range(start_time[1], 18):
        for j in range(start_time[0], end_time + 1):
            # Conflict with Julie's schedule
            if [i, j] in julie_schedule:
                time_grid[i][j] = False
            # Conflict with Sean's schedule
            if [i, j] in sean_schedule:
                time_grid[i][j] = False
            # Conflict with Lori's schedule
            if [i, j] in lori_schedule:
                time_grid[i][j] = False

    # Meeting duration constraint
    for i in range(start_time[1], 18):
        for j in range(start_time[0], end_time - duration + 1):
            if time_grid[i][j] and time_grid[i][j + duration]:
                time_grid[i][j + duration] = False

    # Find a valid time slot
    for i in range(start_time[1], 18):
        for j in range(start_time[0], end_time - duration + 1):
            if time_grid[i][j]:
                return f"SOLUTION:\nDay: {day}\nStart Time: {j:02d}:00\nEnd Time: {(j + duration):02d}:00"

    return "No valid time slot found"

# Example usage
julie_schedule = [[9, 30], [11, 30], [12, 30], [13, 30], [16, 0]]
sean_schedule = [[9, 30], [13, 0], [15, 30], [16, 30]]
lori_schedule = [[10, 30], [11, 30], [12, 30], [13, 0], [15, 30]]
duration = 1

print(schedule_meeting(julie_schedule, sean_schedule, lori_schedule, duration))