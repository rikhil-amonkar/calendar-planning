from z3 import Optimize, Int, Or, sat

# Helper functions to convert times between string and minutes.
def time_to_minutes(t):
    # Converts a time string "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight back to a time string "HH:MM".
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # duration is half an hour
work_start = time_to_minutes("9:00")   # 9:00 AM -> 540 minutes
work_end   = time_to_minutes("17:00")   # 5:00 PM -> 1020 minutes

# Busy intervals on Monday for each participant.

# Christine's meetings: 11:00 to 11:30, 15:00 to 15:30.
christine_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Helen's calendar blocks: 9:30 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:30 to 16:00, 16:30 to 17:00.
helen_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start in minutes since midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to lie within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helen cannot meet after 15:00, so the meeting must finish by 15:00.
opt.add(meeting_end <= time_to_minutes("15:00"))

# Helper function to add non-overlapping constraints given a list of busy intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either end before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add the busy constraints for each participant.
add_busy_constraints(christine_busy)
add_busy_constraints(helen_busy)

# Objective: choose the earliest meeting start time.
opt.minimize(meeting_start)

# Solve and print the chosen meeting time.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")