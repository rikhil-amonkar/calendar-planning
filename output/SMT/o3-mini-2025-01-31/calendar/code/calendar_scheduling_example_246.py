from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings.
def time_to_minutes(time_str):
    # Convert "HH:MM" to minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Convert minutes since midnight back to "HH:MM" format.
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration
meeting_duration = 30  # 30 minutes long meeting.
work_start = time_to_minutes("9:00")   # 540 minutes after midnight.
work_end = time_to_minutes("17:00")    # 1020 minutes after midnight.

# Busy intervals for each participant on Monday. 
# The meeting must not overlap any of these intervals.

# Jacob is busy during:
# 13:30 to 14:00 and 14:30 to 15:00.
jacob_busy = [
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Diana is busy during:
# 9:30 to 10:00, 11:30 to 12:00, 13:00 to 13:30, and 16:00 to 16:30.
diana_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Adam is busy during:
# 9:30 to 10:30, 11:00 to 12:30, and 15:30 to 16:00.
adam_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("12:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Angela is busy during:
# 9:30 to 10:00, 10:30 to 12:00, 13:00 to 15:30, and 16:00 to 16:30.
angela_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Dennis is busy during:
# 9:00 to 9:30, 10:30 to 11:30, 13:00 to 15:00, and 16:30 to 17:00.
dennis_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("13:00"), time_to_minutes("15:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create an Optimize solver.
opt = Optimize()

# Decision variable: meeting start time (in minutes after midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting time to fall within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add constraints so the meeting doesn't overlap a busy interval.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end at or before the busy interval starts, 
        # or it must start at or after the busy interval ends.
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add constraints for each participant.
add_busy_constraints(jacob_busy)
add_busy_constraints(diana_busy)
add_busy_constraints(adam_busy)
add_busy_constraints(angela_busy)
add_busy_constraints(dennis_busy)

# Objective: To schedule the meeting as early in the day as possible.
opt.minimize(meeting_start)

# Check if a valid time exists.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")