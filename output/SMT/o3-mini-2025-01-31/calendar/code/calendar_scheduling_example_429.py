from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings.
def time_to_minutes(time_str):
    # Convert a time string "HH:MM" into minutes since midnight.
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    # Convert minutes since midnight back to a "HH:MM" string.
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # meeting duration in minutes.
work_start = time_to_minutes("9:00")   # 9:00 => 540 minutes.
work_end = time_to_minutes("17:00")    # 17:00 => 1020 minutes.

# Busy intervals for each participant (all times in minutes):

# Judy is busy during:
# 13:00-13:30 and 16:00-16:30.
judy_busy = [
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Olivia is busy during:
# 10:00-10:30, 12:00-13:00, 14:00-14:30.
olivia_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30"))
]

# Eric is free all day.
eric_busy = []  # No busy intervals.

# Jacqueline is busy during:
# 10:00-10:30, 15:00-15:30.
jacqueline_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Laura is busy during:
# 9:00-10:00, 10:30-12:00, 13:00-13:30, 14:30-15:00, 15:30-17:00.
laura_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Tyler is busy during:
# 9:00-10:00, 11:00-11:30, 12:30-13:00, 14:00-14:30, 15:30-17:00.
tyler_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("10:00")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Lisa is busy during:
# 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:00-13:30, 14:00-14:30, 16:00-17:00.
lisa_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Create an Optimize solver.
opt = Optimize()

# Decision variable: meeting start time in minutes from midnight.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to occur within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add constraints to avoid overlapping with busy intervals.
def add_busy_constraints(busy_intervals):
    for start, end in busy_intervals:
        # The meeting must finish before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= start, meeting_start >= end))

# Add constraints for each participant.
add_busy_constraints(judy_busy)
add_busy_constraints(olivia_busy)
add_busy_constraints(eric_busy)      # Eric is free.
add_busy_constraints(jacqueline_busy)
add_busy_constraints(laura_busy)
add_busy_constraints(tyler_busy)
add_busy_constraints(lisa_busy)

# Objective: schedule the meeting at the earliest possible time.
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