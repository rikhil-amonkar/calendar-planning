from z3 import *

# Define the days and possible start times
days = ["Monday", "Tuesday", "Wednesday"]
start_times = [9.0, 9.5, 10.0, 10.5, 11.0, 11.5, 12.0, 12.5, 13.0, 13.5, 14.0, 14.5, 15.0, 15.5, 16.0]

# Create a solver instance
solver = Solver()

# Define Amy's busy times
amy_busy_times = {
    "Wednesday": [(11.0, 11.5), (13.5, 14.0)]
}

# Define Pamela's busy times
pamela_busy_times = {
    "Monday": [(9.0, 10.5), (11.0, 16.5)],
    "Tuesday": [(9.0, 9.5), (10.0, 17.0)],
    "Wednesday": [(9.0, 9.5), (10.0, 11.0), (11.5, 13.5), (14.5, 15.0), (16.0, 16.5)]
}

# Function to check if a time is available
def is_available(day, start_time, busy_times):
    for start, end in busy_times.get(day, []):
        if start_time < end and start_time + 0.5 > start:
            return False
    return True

# Iterate over each day and start time to find a valid meeting time
for day_index, day in enumerate(days):
    for start_time in start_times:
        if start_time + 0.5 > 16.0:
            continue  # Skip invalid start times that exceed 16:00
        if day == "Monday" and start_time < 16.0:
            continue  # Avoid Monday before 16:00
        if day == "Tuesday" and start_time < 16.0:
            continue  # Avoid Tuesday before 16:00
        if day == "Wednesday" and start_time < 16.0:
            continue  # Avoid Wednesday before 16:00
        if is_available(day, start_time, amy_busy_times) and is_available(day, start_time, pamela_busy_times):
            end_time = start_time + 0.5
            start_time_str = f"{int(start_time):02}:{int((start_time % 1) * 60):02}"
            end_time_str = f"{int(end_time):02}:{int((end_time % 1) * 60):02}"
            print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
            break
    else:
        continue
    break
else:
    print("No solution found")