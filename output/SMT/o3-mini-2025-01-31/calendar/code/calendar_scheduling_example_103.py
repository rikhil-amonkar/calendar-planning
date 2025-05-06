from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    # Convert "HH:MM" format to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight to "HH:MM" format.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # half-hour meeting
work_start = time_to_minutes("9:00")    # work start time
work_end   = time_to_minutes("17:00")   # work end time

# Busy intervals on Monday.

# Diane is busy from 9:30 to 10:00 and 14:30 to 15:00.
diane_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Jack is busy from 13:30 to 14:00 and 14:30 to 15:00.
jack_busy = [
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Eugene is busy from 9:00 to 10:00, 10:30 to 11:30, 12:00 to 14:30 and 15:00 to 16:30.
eugene_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:30"))
]

# Patricia is busy from 9:30 to 10:30, 11:00 to 12:00, 12:30 to 14:00 and 15:00 to 16:30.
patricia_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:00"), time_to_minutes("16:30"))
]

# Create a Z3 optimizer.
opt = Optimize()

# Decision variable: meeting_start (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Ensure the meeting is within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add constraints so that the meeting does not overlap busy intervals.
def add_busy_constraints(busy_list):
    for start, end in busy_list:
        # The meeting must end before the busy interval starts or start after the busy interval ends.
        opt.add(Or(meeting_end <= start, meeting_start >= end))

# Add busy constraints for all participants.
add_busy_constraints(diane_busy)
add_busy_constraints(jack_busy)
add_busy_constraints(eugene_busy)
add_busy_constraints(patricia_busy)

# Set objective: choose the earliest possible meeting time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")