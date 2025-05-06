from z3 import Optimize, Int, Or, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Convert "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight back to "HH:MM" format.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM (540 minutes)
work_end   = time_to_minutes("17:00")   # 5:00 PM (1020 minutes)

# Busy intervals on Monday for each participant.
# John: 11:30-12:00, 14:00-14:30.
john_busy = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30"))
]

# Megan: 12:00-12:30, 14:00-15:00, 15:30-16:00.
megan_busy = [
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("14:00"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Brandon: no meetings.
brandon_busy = []  # No busy intervals.

# Kimberly: 9:00-9:30, 10:00-10:30, 11:00-14:30, 15:00-16:00, 16:30-17:00.
kimberly_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Sean: 10:00-11:00, 11:30-14:00, 15:00-15:30.
sean_busy = [
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Lori: 9:00-9:30, 10:30-12:00, 13:00-14:30, 16:00-16:30.
lori_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("14:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Create a Z3 optimizer.
opt = Optimize()

# Decision variable: the meeting start time (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting time to lie within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add busy constraints: the meeting must not overlap with busy intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # Meeting must end before a busy interval starts OR start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add busy constraints for each participant.
add_busy_constraints(john_busy)
add_busy_constraints(megan_busy)
add_busy_constraints(brandon_busy)  # This one adds nothing.
add_busy_constraints(kimberly_busy)
add_busy_constraints(sean_busy)
add_busy_constraints(lori_busy)

# Objective: schedule the meeting at the earliest available time.
opt.minimize(meeting_start)

# Solve and print the solution.
if opt.check() == sat:
    model = opt.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")