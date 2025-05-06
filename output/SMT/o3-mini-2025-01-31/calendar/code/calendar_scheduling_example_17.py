from z3 import Optimize, Int, Or, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Convert "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight back to "HH:MM".
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")   # 9:00 -> 540 minutes.
work_end = time_to_minutes("17:00")    # 17:00 -> 1020 minutes.

# Busy intervals on Monday for each participant.
# Each busy interval is represented as (start_time, end_time) in minutes.

# Margaret's busy intervals.
margaret_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Donna's busy intervals.
donna_busy = [
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Helen's busy intervals.
helen_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Helen's personal preference:
# Helen does not want to meet on Monday after 13:30.
# We enforce that the meeting must finish by 13:30.
helen_preference_end = time_to_minutes("13:30")

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting start time in minutes (on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# The meeting must occur within working hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Add Helen's preference that the meeting ends by 13:30.
opt.add(meeting_end <= helen_preference_end)

# Function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must finish before a busy interval starts
        # or start after it finishes.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for each participant.
add_busy_constraints(margaret_busy)
add_busy_constraints(donna_busy)
add_busy_constraints(helen_busy)

# To meet at the earliest possible time, minimize the meeting start time.
opt.minimize(meeting_start)

if opt.check() == sat:
    model = opt.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")