from z3 import *

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the possible meeting days and times
days = ["Monday", "Tuesday", "Wednesday"]
start_times = [9*60, 9*60+30, 10*60, 10*60+30, 11*60, 11*60+30, 12*60, 12*60+30, 13*60, 13*60+30, 14*60, 14*60+30, 15*60, 15*60+30, 16*60, 16*60+30]  # in minutes from 00:00

# Convert times to strings for easier interpretation
time_strings = {time: f"{time//60:02}:{time%60:02}" for time in start_times}

# Define the constraints for Arthur and Michael
arthur_unavailable = {
    "Monday": [(11*60, 11*60+30), (13*60+30, 14*60), (15*60, 15*60+30)],
    "Tuesday": [(13*60, 13*60+30), (16*60, 16*60+30)],
    "Wednesday": [(10*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (14*60, 14*60+30), (16*60, 16*60+30)]
}

michael_unavailable = {
    "Monday": [(9*60, 12*60), (12*60+30, 13*60), (14*60, 14*60+30), (15*60, 17*60)],
    "Tuesday": [(9*60+30, 11*60+30), (12*60, 13*60+30), (14*60, 15*60+30)],
    "Wednesday": [(10*60, 12*60+30), (13*60, 13*60+30)]
}

# Arthur cannot meet on Tuesday
arthur_unavailable["Tuesday"] = [(9*60, 17*60)]

# Create a solver instance
solver = Solver()

# Define the variables for the meeting day and start time
day_var = Int('day')
start_time_var = Int('start_time')

# Add constraints for the day and start time
solver.add(day_var >= 0)
solver.add(day_var < len(days))
solver.add(start_time_var >= min(start_times))
solver.add(start_time_var <= max(start_times))

# Helper function to check if a time is unavailable
def is_unavailable(day_idx, time, unavailable_times):
    for start, end in unavailable_times:
        if start <= time < end:
            return True
    return False

# Add constraints to avoid unavailable times for Arthur and Michael
for i, day in enumerate(days):
    for start_time in start_times:
        end_time = start_time + meeting_duration
        if is_unavailable(i, start_time, arthur_unavailable[day]) or is_unavailable(i, start_time, michael_unavailable[day]):
            solver.add(Or(day_var != i, start_time_var != start_time))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = days[model[day_var].as_long()]
    meeting_start_time = time_strings[model[start_time_var].as_long()]
    meeting_end_time = time_strings[model[start_time_var].as_long() + meeting_duration]
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")