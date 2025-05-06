from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings.
def time_to_minutes(time_str):
    # Converts a time string "HH:MM" into minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(total_minutes):
    # Converts minutes since midnight into a "HH:MM" string.
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 30  # meeting length in minutes
work_start = time_to_minutes("9:00")   # 9:00 AM => 540 minutes
work_end   = time_to_minutes("17:00")   # 5:00 PM  => 1020 minutes

# Busy intervals for each participant (all times in minutes):

# Bradley's busy intervals:
# 9:30-10:00, 12:30-13:00, 13:30-14:00, 15:30-16:00.
bradley_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Teresa's busy intervals:
# 10:30-11:00, 12:00-12:30, 13:00-13:30, 14:30-15:00.
teresa_busy = [
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Elizabeth's busy intervals:
# 9:00-9:30, 10:30-11:30, 13:00-13:30, 14:30-15:00, 15:30-17:00.
elizabeth_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Christian's busy intervals:
# 9:00-9:30, 10:30-17:00.
christian_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("17:00"))
]

# Create an Optimize solver.
opt = Optimize()

# Decision variable for meeting start time in minutes since midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to occur within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function: For each busy interval, add constraint ensuring the meeting does not overlap.
def add_busy_constraints(busy_intervals):
    for start, end in busy_intervals:
        # Meeting must either end before the busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= start, meeting_start >= end))

# Add busy constraints for each participant.
add_busy_constraints(bradley_busy)
add_busy_constraints(teresa_busy)
add_busy_constraints(elizabeth_busy)
add_busy_constraints(christian_busy)

# Objective: Schedule the meeting as early as possible.
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