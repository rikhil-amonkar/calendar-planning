from z3 import *

# Function to convert time in "HH:MM" format to minutes since midnight.
def to_minutes(time_str):
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

# Function to convert minutes since midnight back to "HH:MM" format.
def to_time_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting duration in minutes.
duration = 60

# Working hours (Monday): 9:00 to 17:00.
work_start = to_minutes("09:00")  # 540 minutes
work_end = to_minutes("17:00")     # 1020 minutes

# Create a Z3 solver instance.
solver = Solver()

# Create an integer variable representing the meeting's start time (in minutes since midnight).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + duration

# Constrain the meeting to lie within working hours.
solver.add(meeting_start >= work_start)
solver.add(meeting_end <= work_end)

# Define busy intervals for each participant (times in minutes since midnight).
# Each busy interval is a tuple: (start, end)
busy_times = {
    "Olivia": [(to_minutes("12:30"), to_minutes("13:30")),
               (to_minutes("14:30"), to_minutes("15:00")),
               (to_minutes("16:30"), to_minutes("17:00"))],
    "Anna":   [],  # Anna is free all day.
    "Virginia": [(to_minutes("09:00"), to_minutes("10:00")),
                 (to_minutes("11:30"), to_minutes("16:00")),
                 (to_minutes("16:30"), to_minutes("17:00"))],
    "Paul":   [(to_minutes("09:00"), to_minutes("09:30")),
               (to_minutes("11:00"), to_minutes("11:30")),
               (to_minutes("13:00"), to_minutes("14:00")),
               (to_minutes("14:30"), to_minutes("16:00")),
               (to_minutes("16:30"), to_minutes("17:00"))]
}

# For each participant's busy interval, ensure the meeting does NOT overlap.
# That is, for every busy interval [b_start, b_end) we require either:
#   meeting_end <= b_start  OR  meeting_start >= b_end
for participant, intervals in busy_times.items():
    for (b_start, b_end) in intervals:
        solver.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Attempt to solve the scheduling constraints.
if solver.check() == sat:
    model = solver.model()
    start_time_val = model[meeting_start].as_long()
    end_time_val = start_time_val + duration

    # Prepare the final solution string in the exact required format.
    solution = "SOLUTION:\n"
    solution += "Day: Monday\n"
    solution += "Start Time: " + to_time_str(start_time_val) + "\n"
    solution += "End Time: " + to_time_str(end_time_val)
    print(solution)
else:
    print("No solution found.")