from z3 import Optimize, Int, Or, sat

# Helper functions to convert times.
def time_to_minutes(t):
    # Converts "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight back to "HH:MM".
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")    # 9:00 -> 540 minutes.
work_end   = time_to_minutes("17:00")    # 17:00 -> 1020 minutes.

# Busy intervals on Monday.
# Each busy interval is represented as (start_time, end_time) in minutes.

# Shirley is busy on Monday during 10:30 to 11:00, 12:00 to 12:30.
shirley_busy = [
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30"))
]

# Jacob is busy on Monday during 9:00 to 9:30, 10:00 to 10:30,
# 11:00 to 11:30, 12:30 to 13:30, 14:30 to 15:00.
jacob_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Stephen is busy on Monday during 11:30 to 12:00, 12:30 to 13:00.
stephen_busy = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00"))
]

# Margaret is busy on Monday during 9:00 to 9:30, 10:30 to 12:30,
# 13:00 to 13:30, 15:00 to 15:30, 16:30 to 17:00.
margaret_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]
# Margaret also does not want to meet on Monday before 14:30.
margaret_preference = time_to_minutes("14:30")

# Mason is busy on Monday during 9:00 to 10:00, 10:30 to 11:00,
# 11:30 to 12:30, 13:00 to 13:30, 14:00 to 14:30, 16:30 to 17:00.
mason_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create an Optimize solver.
opt = Optimize()

# Decision variable: meeting start time in minutes (on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# The meeting must take place within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Enforce Margaret's preference: do not meet before 14:30.
opt.add(meeting_start >= margaret_preference)

# Function to add constraints preventing a meeting from overlapping a busy interval.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add constraints for every participant.
add_busy_constraints(shirley_busy)
add_busy_constraints(jacob_busy)
add_busy_constraints(stephen_busy)
add_busy_constraints(margaret_busy)
add_busy_constraints(mason_busy)

# Objective: Schedule at the earliest available time.
opt.minimize(meeting_start)

# Check for a valid solution.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")