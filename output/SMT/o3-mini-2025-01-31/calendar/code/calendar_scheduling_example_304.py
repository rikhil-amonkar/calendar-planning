from z3 import Optimize, Int, Or, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Converts a time string "HH:MM" into minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight into "HH:MM" format.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # duration in minutes
work_start = time_to_minutes("9:00")    # 9:00 => 540 minutes
work_end   = time_to_minutes("17:00")    # 17:00 => 1020 minutes

# Busy intervals for each participant on Monday. Each tuple is (start, end) in minutes.

# Christine is busy during:
# 9:30-10:30, 12:00-12:30, 13:00-13:30, 14:30-15:00, 16:00-16:30.
christine_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Janice has a free schedule but prefers not to meet after 13:00.
# We enforce that the meeting must finish no later than 13:00.
janice_meeting_deadline = time_to_minutes("13:00")

# Bobby is busy during:
# 12:00-12:30, 14:30-15:00.
bobby_busy = [
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Elizabeth is busy during:
# 9:00-9:30, 11:30-13:00, 13:30-14:00, 15:00-15:30, 16:00-17:00.
elizabeth_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Tyler is busy during:
# 9:00-11:00, 12:00-12:30, 13:00-13:30, 15:30-16:00, 16:30-17:00.
tyler_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Edward is busy during:
# 9:00-9:30, 10:00-11:00, 11:30-14:00, 14:30-15:30, 16:00-17:00.
edward_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Create a Z3 Optimize solver.
opt = Optimize()

# Decision variable for meeting start time in minutes since midnight.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting within the work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Enforce Janice's preference: the meeting must finish by 13:00.
opt.add(meeting_end <= janice_meeting_deadline)

# Function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either end before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for all participants.
add_busy_constraints(christine_busy)
# Janice has no busy intervals besides her meeting preference.
add_busy_constraints(bobby_busy)
add_busy_constraints(elizabeth_busy)
add_busy_constraints(tyler_busy)
add_busy_constraints(edward_busy)

# Objective: schedule at the earliest time available.
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