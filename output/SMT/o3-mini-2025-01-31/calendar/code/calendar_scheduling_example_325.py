from z3 import Optimize, Int, Or, sat

# Helper functions for converting time strings.
def time_to_minutes(time_str):
    # Converts a time string "HH:MM" into total minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(total_minutes):
    # Converts minutes since midnight back to "HH:MM" format.
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 30  # meeting is 30 minutes long
work_start = time_to_minutes("9:00")    # 540 minutes
work_end   = time_to_minutes("17:00")    # 1020 minutes

# Busy intervals for each participant on Monday (in minutes).

# Jose's busy intervals.
jose_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00"))
]
# Jose does not want meetings after 15:30, so we require the meeting to finish by 15:30.

# Keith's busy intervals.
keith_busy = [
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Logan's busy intervals.
logan_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("10:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Megan's busy intervals.
megan_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))
]

# Gary's busy intervals.
gary_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))
]

# Bobby's busy intervals.
bobby_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("16:00"))
]

# Create an Optimize solver.
opt = Optimize()

# Decision variable: meeting start time (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to occur within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Enforce Jose's preference to meet before 15:30 (meeting must finish by 15:30).
jose_deadline = time_to_minutes("15:30")  # 930 minutes
opt.add(meeting_end <= jose_deadline)

# Helper function to add constraints to avoid overlapping a busy interval.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish at or before a busy interval starts or start at or after it ends.
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add busy constraints for all participants.
add_busy_constraints(jose_busy)
add_busy_constraints(keith_busy)
add_busy_constraints(logan_busy)
add_busy_constraints(megan_busy)
add_busy_constraints(gary_busy)
add_busy_constraints(bobby_busy)

# Objective: find the earliest meeting time.
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