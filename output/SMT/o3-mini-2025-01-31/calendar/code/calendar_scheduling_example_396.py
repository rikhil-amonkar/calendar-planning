from z3 import Optimize, Int, Or, sat

# Helper functions for time conversions.
def time_to_minutes(t):
    # Convert time string "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight back to "HH:MM" string.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # half an hour meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM -> 540 minutes.
work_end   = time_to_minutes("17:00")   # 5:00 PM -> 1020 minutes.

# Busy intervals on Monday for each participant.

# Andrea's calendar is wide open.
andrea_busy = []

# Jack is busy during 9:00 to 9:30 and 14:00 to 14:30.
jack_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("14:00"), time_to_minutes("14:30"))
]

# Madison is busy during 9:30 to 10:30, 13:00 to 14:00, 15:00 to 15:30, 16:30 to 17:00.
madison_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Rachel is busy during 9:30 to 10:30, 11:00 to 11:30, 12:00 to 13:30, 14:30 to 15:30, 16:00 to 17:00.
rachel_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Douglas is busy during 9:00 to 11:30 and 12:00 to 16:30.
douglas_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("16:30"))
]

# Ryan is busy during 9:00 to 9:30, 13:00 to 14:00, 14:30 to 17:00.
ryan_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

# List all busy intervals for ease of iteration.
all_busy = [andrea_busy, jack_busy, madison_busy, rachel_busy, douglas_busy, ryan_busy]

# Create the Z3 Optimize solver.
opt = Optimize()

# Define the decision variable: meeting_start (in minutes since midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add non-overlap constraints with busy intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must finish before a busy interval starts or begin after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for each participant.
for busy in all_busy:
    add_busy_constraints(busy)

# Objective: pick the earliest available meeting start time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")