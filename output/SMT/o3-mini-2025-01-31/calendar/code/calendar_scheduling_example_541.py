from z3 import Optimize, Int, Or, sat

# Helper functions to convert between time strings and minutes.
def time_to_minutes(t):
    # t is in "HH:MM" format.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour meeting
work_start = time_to_minutes("9:00")   # 9:00 AM -> 540 minutes
work_end   = time_to_minutes("17:00")   # 5:00 PM -> 1020 minutes

# Busy intervals on Monday.

# Kayla's busy intervals: 10:00 to 10:30, 14:30 to 16:00.
kayla_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("14:30"), time_to_minutes("16:00"))
]

# Rebecca's busy intervals: 9:00 to 13:00, 13:30 to 15:00, 15:30 to 16:00.
rebecca_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to lie within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add constraints for non-overlapping intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # Meeting must either end before a busy interval starts,
        # or start after that busy interval ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for Kayla and Rebecca.
add_busy_constraints(kayla_busy)
add_busy_constraints(rebecca_busy)

# Objective: schedule the meeting at the earliest available time.
opt.minimize(meeting_start)

# Check for a solution and display the meeting time.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")