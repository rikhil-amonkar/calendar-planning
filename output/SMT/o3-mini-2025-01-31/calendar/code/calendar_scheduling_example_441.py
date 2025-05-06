from z3 import Optimize, Int, Or, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Converts a time string "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight to a "HH:MM" time string.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # half-hour meeting.
work_start = time_to_minutes("9:00")   # work day starts at 9:00.
work_end   = time_to_minutes("17:00")   # work day ends at 17:00.

# Busy intervals on Monday for each participant.
# Joan: 11:30 to 12:00, 14:30 to 15:00.
joan_busy = [(time_to_minutes("11:30"), time_to_minutes("12:00")),
             (time_to_minutes("14:30"), time_to_minutes("15:00"))]

# Megan: 9:00 to 10:00, 14:00 to 14:30, 16:00 to 16:30.
megan_busy = [(time_to_minutes("9:00"), time_to_minutes("10:00")),
              (time_to_minutes("14:00"), time_to_minutes("14:30")),
              (time_to_minutes("16:00"), time_to_minutes("16:30"))]

# Austin: free all day, so no busy intervals.
austin_busy = []

# Betty: 9:30 to 10:00, 11:30 to 12:00, 13:30 to 14:00, 16:00 to 16:30.
betty_busy = [(time_to_minutes("9:30"), time_to_minutes("10:00")),
              (time_to_minutes("11:30"), time_to_minutes("12:00")),
              (time_to_minutes("13:30"), time_to_minutes("14:00")),
              (time_to_minutes("16:00"), time_to_minutes("16:30"))]

# Judith: 9:00 to 11:00, 12:00 to 13:00, 14:00 to 15:00.
judith_busy = [(time_to_minutes("9:00"), time_to_minutes("11:00")),
               (time_to_minutes("12:00"), time_to_minutes("13:00")),
               (time_to_minutes("14:00"), time_to_minutes("15:00"))]

# Terry: 9:30 to 10:00, 11:30 to 12:30, 13:00 to 14:00, 15:00 to 15:30, 16:00 to 17:00.
terry_busy = [(time_to_minutes("9:30"), time_to_minutes("10:00")),
              (time_to_minutes("11:30"), time_to_minutes("12:30")),
              (time_to_minutes("13:00"), time_to_minutes("14:00")),
              (time_to_minutes("15:00"), time_to_minutes("15:30")),
              (time_to_minutes("16:00"), time_to_minutes("17:00"))]

# Kathryn: 9:30 to 10:00, 10:30 to 11:00, 11:30 to 13:00, 14:00 to 16:00, 16:30 to 17:00.
kathryn_busy = [(time_to_minutes("9:30"), time_to_minutes("10:00")),
                (time_to_minutes("10:30"), time_to_minutes("11:00")),
                (time_to_minutes("11:30"), time_to_minutes("13:00")),
                (time_to_minutes("14:00"), time_to_minutes("16:00")),
                (time_to_minutes("16:30"), time_to_minutes("17:00"))]

# Create a Z3 optimizer.
opt = Optimize()

# Decision variable: meeting_start (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add busy interval constraints.
def add_busy_constraints(busy_intervals):
    for start, end in busy_intervals:
        # The meeting must either finish before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= start, meeting_start >= end))

# Apply busy constraints for all participants.
add_busy_constraints(joan_busy)
add_busy_constraints(megan_busy)
add_busy_constraints(austin_busy)  # Not needed but added for uniformity.
add_busy_constraints(betty_busy)
add_busy_constraints(judith_busy)
add_busy_constraints(terry_busy)
add_busy_constraints(kathryn_busy)

# Objective: choose the earliest possible meeting time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    scheduled_start = model[meeting_start].as_long()
    scheduled_end = scheduled_start + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(scheduled_start))
    print("End:  ", minutes_to_time(scheduled_end))
else:
    print("No valid meeting time could be found.")