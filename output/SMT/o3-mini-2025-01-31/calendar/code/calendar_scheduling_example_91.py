from z3 import Optimize, Int, Or, sat

# Helper functions for converting time strings.
def time_to_minutes(time_str):
    # Convert time string "HH:MM" into total minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(total_minutes):
    # Convert total minutes into time string "HH:MM"
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 60  # 1 hour meeting.
work_start = time_to_minutes("9:00")    # 9:00 -> 540 minutes.
work_end   = time_to_minutes("17:00")    # 17:00 -> 1020 minutes.

# Busy intervals for each participant (all times in minutes):

# Danielle's busy intervals:
# 9:00 to 10:00, 10:30 to 11:00, 14:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00.
danielle_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Bruce's busy intervals:
# 11:00 to 11:30, 12:30 to 13:00, 14:00 to 14:30, 15:30 to 16:00.
bruce_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Eric's busy intervals:
# 9:00 to 9:30, 10:00 to 11:00, 11:30 to 13:00, 14:30 to 15:30.
eric_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30"))
]

# Create an Optimize solver.
opt = Optimize()

# Decision variable: meeting start time in minutes since midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to occur within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Define a function that prevents the meeting from overlapping with busy intervals.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either finish before a busy interval starts or begin after it ends.
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add constraints for Danielle, Bruce, and Eric.
add_busy_constraints(danielle_busy)
add_busy_constraints(bruce_busy)
add_busy_constraints(eric_busy)

# Objective: schedule the meeting at the earliest possible time.
opt.minimize(meeting_start)

if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")