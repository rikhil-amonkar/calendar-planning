from z3 import Optimize, Int, Or, sat

# Helper functions to convert times between string format and minutes.
def time_to_minutes(t):
    # Converts a time string "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight back to a time string "HH:MM".
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30 minutes meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM (540 minutes)
work_end   = time_to_minutes("17:00")   # 5:00 PM (1020 minutes)

# Busy intervals on Monday.
# Denise is busy during 12:00 to 12:30 and 15:30 to 16:00.
denise_busy = [
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Angela has no meetings, so no busy intervals for her.
angel_busy = []  # Not required in constraints.

# Natalie is busy during 9:00 to 11:30, 12:00 to 13:00, 14:00 to 14:30, 15:00 to 17:00.
natalie_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("17:00"))
]

# Create Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start represents the start time (in minutes) on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to lie within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add busy constraints: Meeting must either finish before a busy interval starts or start after it ends.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for Denise and Natalie.
add_busy_constraints(denise_busy)
add_busy_constraints(natalie_busy)

# Angela has no busy intervals, so no extra constraints.

# Objective: Schedule the meeting at the earliest available time.
opt.minimize(meeting_start)

# Solve and output the meeting time.
if opt.check() == sat:
    model = opt.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")