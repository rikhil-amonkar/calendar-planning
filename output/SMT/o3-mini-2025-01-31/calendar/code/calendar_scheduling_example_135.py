from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings to minutes since midnight and back.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # minutes
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Busy intervals for each participant on Monday:
# Eric is free all day.

# Ashley's busy intervals:
# 10:00 to 10:30, 11:00 to 12:00, 12:30 to 13:00, 15:00 to 16:00.
ashley_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("15:00"), time_to_minutes("16:00"))
]

# Ronald's busy intervals:
# 9:00 to 9:30, 10:00 to 11:30, 12:30 to 14:00, 14:30 to 17:00.
ronald_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

# Larry's busy intervals:
# 9:00 to 12:00, 13:00 to 17:00.
larry_busy = [
    (time_to_minutes("9:00"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("17:00"))
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start time (in minutes from midnight on Monday)
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add busy constraints: meeting must not overlap with any busy interval.
def add_busy_constraints(busy_intervals):
    for start, end in busy_intervals:
        # The meeting must either finish before the busy interval starts 
        # or start after the busy interval ends.
        opt.add(Or(meeting_end <= start, meeting_start >= end))

# Add constraints for Ashley, Ronald, and Larry.
add_busy_constraints(ashley_busy)
add_busy_constraints(ronald_busy)
add_busy_constraints(larry_busy)

# Objective: meet at the earliest possible time.
opt.minimize(meeting_start)

# Check and print a solution.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")