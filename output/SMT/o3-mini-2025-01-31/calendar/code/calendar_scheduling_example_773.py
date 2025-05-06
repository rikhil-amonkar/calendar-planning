from z3 import Optimize, Int, Or, Implies, sat

# Helper functions to convert time strings into minutes and vice versa.
def time_to_minutes(t):
    # Converts "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight back into "HH:MM" format.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # 1 hour meeting.
work_start = time_to_minutes("9:00")   # 540 minutes.
work_end = time_to_minutes("17:00")    # 1020 minutes.

# Allowed days: 0 -> Monday, 1 -> Tuesday, 2 -> Wednesday.
allowed_days = [0, 1, 2]

# Roy's busy intervals per day (in minutes).
# Monday:
roy_monday_busy = [
    (time_to_minutes("10:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("17:00"))
]
# Tuesday:
roy_tuesday_busy = [
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]
# Wednesday:
roy_wednesday_busy = [
    (time_to_minutes("9:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Patrick is completely free, so there are no constraints for him.

# Create an Optimize solver.
opt = Optimize()

# Decision variables.
meeting_day = Int("meeting_day")
# Only allow meeting day to be Monday (0), Tuesday (1), or Wednesday (2).
opt.add(Or(meeting_day == allowed_days[0], meeting_day == allowed_days[1], meeting_day == allowed_days[2]))

meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add busy interval constraints for Roy.
def add_roy_busy_constraints(busy_intervals, day_value):
    for busy_start, busy_end in busy_intervals:
        # If the meeting is on this day, then it must not overlap with any busy interval.
        opt.add(Implies(meeting_day == day_value, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Add Roy's busy constraints.
add_roy_busy_constraints(roy_monday_busy, 0)
add_roy_busy_constraints(roy_tuesday_busy, 1)
add_roy_busy_constraints(roy_wednesday_busy, 2)

# Objective: The group would like to meet at their earliest availability.
# We'll minimize a compound objective where earlier day and earlier time are preferred.
opt.minimize(meeting_day * 10000 + meeting_start)

# Check for a valid meeting time.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration

    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")