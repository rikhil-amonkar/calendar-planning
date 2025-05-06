from z3 import Optimize, Int, Or, sat

# Helper functions.
def time_to_minutes(t):
    # Converts time "HH:MM" into minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")    # 9:00 = 540 minutes.
work_end = time_to_minutes("17:00")     # 17:00 = 1020 minutes.

# We only have Monday for this meeting.
# So we fix the day to Monday.

# Busy intervals on Monday for each participant:
# Each busy interval is given as a tuple (start, end) in minutes.
adam_busy = [
    (time_to_minutes("14:00"), time_to_minutes("15:00"))
]

john_busy = [
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

stephanie_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

anna_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]
# Anna's additional preference: rather not meet on Monday before 14:30.
anna_preference_start = time_to_minutes("14:30")

# Create an Optimize solver.
opt = Optimize()

# Decision variable: meeting start time in minutes.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Because the meeting is on Monday only, we add Anna's preference:
opt.add(meeting_start >= anna_preference_start)

# Function to ensure the meeting does not overlap a busy interval.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either finish before the busy interval starts
        # or start after the busy interval ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for each participant.
add_busy_constraints(adam_busy)
add_busy_constraints(john_busy)
add_busy_constraints(stephanie_busy)
add_busy_constraints(anna_busy)

# To find the earliest available meeting time, minimize the meeting_start.
opt.minimize(meeting_start)

# Check for a valid meeting time.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")