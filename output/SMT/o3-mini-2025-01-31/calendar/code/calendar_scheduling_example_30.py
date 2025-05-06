from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    # t should be in "HH:MM" format.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # minutes
work_start = time_to_minutes("9:00")
work_end   = time_to_minutes("17:00")

# Busy intervals on Monday for each participant:
# Jeffrey's busy intervals.
jeffrey_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00"))
]

# Virginia's busy intervals.
virginia_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Melissa's busy intervals.
melissa_busy = [
    (time_to_minutes("9:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start time in minutes from midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within the work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Melissa would rather not meet on Monday after 14:00;
# We add this as a soft constraint, so if possible, the meeting should end by 14:00.
opt.add_soft(meeting_end <= time_to_minutes("14:00"), weight=1)

# Helper function to add busy constraints.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either finish before the busy interval starts
        # or start after the busy interval ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for each participant.
add_busy_constraints(jeffrey_busy)
add_busy_constraints(virginia_busy)
add_busy_constraints(melissa_busy)

# Objective: prefer earlier meeting times by minimizing meeting_start.
opt.minimize(meeting_start)

# Solve and output the result.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")