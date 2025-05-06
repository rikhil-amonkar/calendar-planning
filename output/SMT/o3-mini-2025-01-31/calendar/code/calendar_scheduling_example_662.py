from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert time format.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM
work_end   = time_to_minutes("17:00")   # 5:00 PM

# Allowed days: Monday=0 and Tuesday=1.
allowed_days = [0, 1]

# Busy intervals for Gary.
# Monday busy intervals.
gary_mon = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("11:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]
# Tuesday busy intervals.
gary_tue = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:00"))
]

gary_busy = {0: gary_mon, 1: gary_tue}

# Busy intervals for David.
# Monday busy intervals.
david_mon = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))
]
# Tuesday busy intervals.
david_tue = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

david_busy = {0: david_mon, 1: david_tue}

# Create Z3 optimizer.
opt = Optimize()

# Decision variables:
# meeting_day: 0 for Monday, 1 for Tuesday.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: meeting start time (in minutes from midnight) on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting time within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add busy constraints.
def add_busy_constraints(schedule):
    for day in allowed_days:
        for b_start, b_end in schedule.get(day, []):
            # If meeting is scheduled on that day, it must not overlap the busy interval.
            opt.add(If(meeting_day == day,
                       Or(meeting_end <= b_start, meeting_start >= b_end),
                       True))

# Add busy constraints for Gary and David.
add_busy_constraints(gary_busy)
add_busy_constraints(david_busy)

# Optionally, set an objective to choose the earliest meeting time (across days and times).
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration

    day_names = {0: "Monday", 1: "Tuesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")