from z3 import Optimize, Int, Or, Implies, If, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # Half an hour.
work_start = time_to_minutes("9:00")   # 9:00 -> 540 minutes.
work_end = time_to_minutes("17:00")    # 17:00 -> 1020 minutes.

# Days encoding.
# 0 -> Monday, 1 -> Tuesday, 2 -> Wednesday, 3 -> Thursday, 4 -> Friday
allowed_days = [0, 1, 2, 3, 4]

# Busy intervals for Eugene (per day):
# Monday:
eugene_monday = [
    (time_to_minutes("11:00"), time_to_minutes("12:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]
# Tuesday: Eugene is free (no busy intervals).
eugene_tuesday = []
# Wednesday:
eugene_wednesday = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("15:00"))
]
# Thursday:
eugene_thursday = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("11:00"), time_to_minutes("12:30"))
]
# Friday:
eugene_friday = [
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30"))
]

# Busy intervals for Eric (per day):
# Monday: busy entire day
eric_monday = [
    (time_to_minutes("9:00"), time_to_minutes("17:00"))
]
# Tuesday: busy entire day
eric_tuesday = [
    (time_to_minutes("9:00"), time_to_minutes("17:00"))
]
# Wednesday:
eric_wednesday = [
    (time_to_minutes("9:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))
]
# Thursday: busy entire day.
eric_thursday = [
    (time_to_minutes("9:00"), time_to_minutes("17:00"))
]
# Friday:
eric_friday = [
    (time_to_minutes("9:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("17:00"))
]

# Create an Optimize object for solving and optional preference.
opt = Optimize()

# Decision variables.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper to add non-overlap constraints for a set of busy intervals on a given day.
def add_busy_constraints(busy_intervals, day_val):
    for start_busy, end_busy in busy_intervals:
        # If meeting is on `day_val`, then it must either end by busy start or start after busy end.
        opt.add(Implies(meeting_day == day_val, Or(meeting_end <= start_busy, meeting_start >= end_busy)))

# Add constraints for Eugene.
add_busy_constraints(eugene_monday, 0)
add_busy_constraints(eugene_tuesday, 1)
add_busy_constraints(eugene_wednesday, 2)
add_busy_constraints(eugene_thursday, 3)
add_busy_constraints(eugene_friday, 4)

# Add constraints for Eric.
add_busy_constraints(eric_monday, 0)
add_busy_constraints(eric_tuesday, 1)
add_busy_constraints(eric_wednesday, 2)
add_busy_constraints(eric_thursday, 3)
add_busy_constraints(eric_friday, 4)

# Eric would like to avoid more meetings on Wednesday.
# We add a soft constraint (penalty) that penalizes scheduling on Wednesday.
penalty = If(meeting_day == 2, 1, 0)
opt.minimize(penalty)

# Additionally, to choose the earliest available time in the day,
# we minimize the meeting start time as a secondary objective.
opt.minimize(meeting_start)

# Check for a valid meeting time.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")