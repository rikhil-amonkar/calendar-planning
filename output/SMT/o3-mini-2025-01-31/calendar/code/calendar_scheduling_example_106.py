from z3 import Optimize, Int, Or, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Convert time string "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight to time string "HH:MM".
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one-hour meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM (540 minutes)
work_end   = time_to_minutes("17:00")   # 5:00 PM (1020 minutes)

# Busy intervals on Monday.
# Olivia is busy during 12:30-13:30, 14:30-15:00, and 16:30-17:00.
olivia_busy = [
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Anna has no meetings all day.
anna_busy = []  # No busy time.

# Virginia is busy on Monday during 9:00-10:00, 11:30-16:00, and 16:30-17:00.
virginia_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("11:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Paul is busy on Monday during 9:00-9:30, 11:00-11:30, 13:00-14:00, 14:30-16:00, and 16:30-17:00.
paul_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start in minutes since midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add non-overlapping constraints for a list of busy intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting should either end before b_start or start after b_end.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add busy constraints for each participant.
add_busy_constraints(olivia_busy)
add_busy_constraints(virginia_busy)
add_busy_constraints(paul_busy)
# Anna has no busy intervals.

# Objective: find the earliest available meeting time.
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