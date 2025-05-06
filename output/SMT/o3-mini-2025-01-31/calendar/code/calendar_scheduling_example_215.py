from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # minutes
work_start = time_to_minutes("9:00")   # 540 minutes
work_end = time_to_minutes("17:00")      # 1020 minutes

# Busy intervals for each participant on Monday.
# Steven is free all day, Roy is free all day, so we add constraints only for Cynthia, Lauren, and Robert.

# Cynthia is busy on Monday during:
# 9:30 to 10:30, 11:30 to 12:00, 13:00 to 13:30, 15:00 to 16:00.
cynthia_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:00"))
]

# Lauren has meetings on Monday during:
# 9:00 to 9:30, 10:30 to 11:00, 11:30 to 12:00, 13:00 to 13:30,
# 14:00 to 14:30, 15:00 to 15:30, 16:00 to 17:00.
lauren_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Robert has blocked his calendar on Monday during:
# 10:30 to 11:00, 11:30 to 12:00, 12:30 to 13:30, 14:00 to 16:00.
robert_busy = [
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:00"))
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start (in minutes since midnight Monday)
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within working hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must finish before the busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add busy constraints for Cynthia.
add_busy_constraints(cynthia_busy)
# Add busy constraints for Lauren.
add_busy_constraints(lauren_busy)
# Add busy constraints for Robert.
add_busy_constraints(robert_busy)

# Objective: minimize meeting_start to schedule at the earliest availability.
opt.minimize(meeting_start)

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")