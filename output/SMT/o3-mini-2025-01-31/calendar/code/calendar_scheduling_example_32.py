from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings to minutes and back.
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 30  # minutes
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Busy intervals for each participant on Monday (in minutes).

# Emily's busy intervals:
# 10:00-10:30, 11:30-12:30, 14:00-15:00, 16:00-16:30.
emily_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("14:00"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Melissa's busy intervals:
# 9:30-10:00, 14:30-15:00.
melissa_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Frank's busy intervals:
# 10:00-10:30, 11:00-11:30, 12:30-13:00, 13:30-14:30, 15:00-16:00, 16:30-17:00.
frank_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Additional constraint: Frank does not want to meet on Monday after 9:30,
# so the meeting must be finished by 9:30.
frank_preference_deadline = time_to_minutes("9:30")

# Create an Optimize solver.
opt = Optimize()

# Decision variable: meeting start time (minutes from midnight on Monday)
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to be during work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Add Frank's preference: meeting must end by 9:30
opt.add(meeting_end <= frank_preference_deadline)

# Helper function to add constraints preventing any overlap with busy intervals.
def add_busy_constraints(busy_intervals):
    for start, end in busy_intervals:
        # The meeting must either end before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= start, meeting_start >= end))

# Add busy constraints for each participant.
add_busy_constraints(emily_busy)
add_busy_constraints(melissa_busy)
add_busy_constraints(frank_busy)

# Objective: schedule the meeting as early as possible.
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