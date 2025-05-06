from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings to minutes after midnight and back.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration
meeting_duration = 30  # duration in minutes
work_start = time_to_minutes("9:00")   # start of work day (540 minutes)
work_end   = time_to_minutes("17:00")   # end of work day (1020 minutes)

# Billy would prefer not to have meetings after 15:00.
# So we impose that the meeting must finish by 15:00.
latest_meeting_end_for_billy = time_to_minutes("15:00")

# Busy intervals for each participant on Monday:
# Raymond's busy intervals:
raymond_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Billy's busy intervals:
billy_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Donald's busy intervals:
donald_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Create Z3 Optimize solver instance.
opt = Optimize()

# Decision variable: meeting_start represents the meeting start time in minutes past midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Apply Billy's preference: meeting must finish by 15:00.
opt.add(meeting_end <= latest_meeting_end_for_billy)

# Helper function to add busy constraints.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either end before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add the constraints for each participant.
add_busy_constraints(raymond_busy)
add_busy_constraints(billy_busy)
add_busy_constraints(donald_busy)

# Objective: choose the earliest possible meeting time.
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