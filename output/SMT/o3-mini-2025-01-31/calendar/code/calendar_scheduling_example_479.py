from z3 import Solver, Int, Or, sat

# Helper functions for converting times.
def time_to_minutes(t):
    # Converts "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight to "HH:MM" format.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM => 540 minutes.
work_end   = time_to_minutes("17:00")  # 5:00 PM => 1020 minutes.

# Busy intervals for each participant on Monday.
# Each interval is a tuple (start, end) in minutes.

# Evelyn is free all day, so no busy intervals.
# Joshua's busy intervals:
#   11:00 to 12:30, 13:30 to 14:30, 16:30 to 17:00.
joshua_busy = [
    (time_to_minutes("11:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Kevin is free all day.
# Gerald is free all day.
# Jerry's busy intervals:
#   9:00 to 9:30, 10:30 to 12:00, 12:30 to 13:00, 13:30 to 14:00, 14:30 to 15:00, 15:30 to 16:00.
jerry_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Jesse's busy intervals:
#   9:00 to 9:30, 10:30 to 12:00, 12:30 to 13:00, 14:30 to 15:00, 15:30 to 16:30.
jesse_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:30"))
]

# Kenneth's busy intervals:
#   10:30 to 12:30, 13:30 to 14:00, 14:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00.
kenneth_busy = [
    (time_to_minutes("10:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create our solver instance.
solver = Solver()

# Decision variable: meeting start time in minutes.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Meeting must occur within work hours.
solver.add(meeting_start >= work_start, meeting_end <= work_end)

# A utility function to add non-overlap constraints for a participant's busy intervals.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must not overlap any busy interval:
        # either it finishes before the busy interval starts, or it starts after the busy interval ends.
        solver.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add constraints for each participant.
add_busy_constraints(joshua_busy)
add_busy_constraints(jerry_busy)
add_busy_constraints(jesse_busy)
add_busy_constraints(kenneth_busy)
# Evelyn, Kevin, and Gerald are free all day so no constraints are needed for them.

# Check if a valid meeting time exists.
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")