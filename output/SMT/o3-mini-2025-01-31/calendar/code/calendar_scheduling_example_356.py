from z3 import Optimize, Int, Or, sat

# Helper functions to convert between time strings and minutes since midnight.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # minutes
work_start = time_to_minutes("9:00")
work_end   = time_to_minutes("17:00")

# This meeting is to be scheduled on Monday.
# Angela would like to avoid meetings before 15:00 on Monday.
angela_preference = time_to_minutes("15:00")

# Busy intervals on Monday for each participant.
# Intervals are represented as (start, end) in minutes.
katherine_busy = [
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:30"))
]
# Rebecca has no meetings.
julie_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]
angela_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]
nicholas_busy = [
    (time_to_minutes("9:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]
carl_busy = [
    (time_to_minutes("9:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start, the start time in minutes from midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to be within working hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Enforce Angela's preference: avoid meetings before 15:00.
opt.add(meeting_start >= angela_preference)

# Helper function to add non-overlap busy constraints.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must finish before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add busy constraints for all participants.
add_busy_constraints(katherine_busy)
# Rebecca is free, so no constraints needed.
add_busy_constraints(julie_busy)
add_busy_constraints(angela_busy)
add_busy_constraints(nicholas_busy)
add_busy_constraints(carl_busy)

# Objective: schedule the meeting at the earliest available time (minimize meeting_start).
opt.minimize(meeting_start)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")