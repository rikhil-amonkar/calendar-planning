from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings to minutes and vice versa.
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

# Busy intervals for each participant (Monday):

# Patrick's busy intervals.
patrick_busy = [
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Shirley's busy intervals.
shirley_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Jeffrey's busy intervals.
jeffrey_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Gloria's busy intervals.
gloria_busy = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Nathan's busy intervals.
nathan_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("14:00"), time_to_minutes("17:00"))
]

# Angela's busy intervals.
angela_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("12:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:30"))
]

# David's busy intervals.
david_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# The meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add non-overlap constraints for a given set of busy intervals.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting must not overlap with the busy interval:
        # It must finish before the busy interval starts OR start after the busy interval ends.
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add busy constraints for all participants.
add_busy_constraints(patrick_busy)
add_busy_constraints(shirley_busy)
add_busy_constraints(jeffrey_busy)
add_busy_constraints(gloria_busy)
add_busy_constraints(nathan_busy)
add_busy_constraints(angela_busy)
add_busy_constraints(david_busy)

# Objective: choose the earliest available meeting time by minimizing meeting_start.
opt.minimize(meeting_start)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")