from z3 import Solver, Int, Or

# Convert HH:MM string to minutes from midnight
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

# Format minutes value (minutes from midnight) as "HH:MM" in 24-hour format
def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02}:{m:02}"

# Meeting duration in minutes
duration = 60

# Define working hours for Monday: 09:00 to 17:00.
work_start = time_to_minutes("09:00")  # 540
work_end = time_to_minutes("17:00")    # 1020
# Meeting must finish by work_end so s must be <= work_end - duration.
latest_start = work_end - duration    # 1020 - 60 = 960

# Busy intervals for each person (start, end in minutes)
# Danielle's busy intervals:
danielle_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Bruce's busy intervals:
bruce_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Eric's busy intervals:
eric_busy = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30"))
]

# Combine all busy intervals into one list
all_busy = danielle_busy + bruce_busy + eric_busy

# Create the Z3 solver and variable for meeting start time (in minutes from midnight)
s = Solver()
start = Int("start")

# Meeting must be scheduled within the working hours.
s.add(start >= work_start, start <= latest_start)

# For each busy interval, the meeting [start, start+duration] should not overlap.
# Two intervals [a, b] and [c, d] do not overlap if (b <= c) or (d <= a).
for busy_start, busy_end in all_busy:
    s.add(Or(start + duration <= busy_start, start >= busy_end))

# Check for a solution.
if s.check().r == 1:
    model = s.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration

    # Format the meeting time as required.
    output = "SOLUTION:\n"
    output += "Day: Monday\n"
    output += f"Start Time: {format_time(meeting_start)}\n"
    output += f"End Time: {format_time(meeting_end)}"
    print(output)
else:
    print("No solution found.")