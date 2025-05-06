from z3 import Optimize, Int, Or, sat

# Helper functions to convert between "HH:MM" strings and minutes.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM -> 540 minutes.
work_end   = time_to_minutes("17:00")   # 5:00 PM -> 1020 minutes.

# Busy intervals on Monday.
# Adam is busy during 9:30-10:00, 12:30-13:00, 14:30-15:00, and 16:30-17:00.
adam_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Roy is busy during 10:00-11:00, 11:30-13:00, 13:30-14:30, and 16:30-17:00.
roy_busy = [
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create a Z3 Optimize solver.
opt = Optimize()

# Define the decision variable for the meeting start time (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within the work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add non-overlapping constraints for a participant's busy intervals.
def add_busy_constraints(busy_intervals):
    for interval_start, interval_end in busy_intervals:
        # The meeting must either finish before a busy interval starts,
        # or start after the busy interval ends.
        opt.add(Or(meeting_end <= interval_start, meeting_start >= interval_end))

# Add busy constraints for Adam and Roy.
add_busy_constraints(adam_busy)
add_busy_constraints(roy_busy)

# Objective: Schedule the meeting at the earliest available time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(chosen_start))
    print("End:  ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")