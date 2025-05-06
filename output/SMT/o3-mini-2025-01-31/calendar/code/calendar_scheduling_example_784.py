from z3 import Optimize, Int, Or, If, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour meeting.
work_start = time_to_minutes("9:00")    # 9:00 AM
work_end   = time_to_minutes("17:00")    # 5:00 PM

# Allowed days: Monday=0, Tuesday=1, Wednesday=2.
allowed_days = [0, 1, 2]

# Busy intervals for Judith.
# Monday: 12:00 to 12:30.
# Wednesday: 11:30 to 12:00.
judith_busy = {
    0: [(time_to_minutes("12:00"), time_to_minutes("12:30"))],
    1: [],  # No busy intervals on Tuesday.
    2: [(time_to_minutes("11:30"), time_to_minutes("12:00"))]
}

# Busy intervals for Timothy.
# Monday: 9:30-10:00, 10:30-11:30, 12:30-14:00, 15:30-17:00.
# Tuesday: 9:30-13:00, 13:30-14:00, 14:30-17:00.
# Wednesday: 9:00-9:30, 10:30-11:00, 13:30-14:30, 15:00-15:30, 16:00-16:30.
timothy_busy = {
    0: [
        (time_to_minutes("9:30"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("14:00")),
        (time_to_minutes("15:30"), time_to_minutes("17:00"))
    ],
    1: [
        (time_to_minutes("9:30"),  time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("17:00"))
    ],
    2: [
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Create a Z3 optimizer.
opt = Optimize()

# Decision variables:
# meeting_day: 0 for Monday, 1 for Tuesday, 2 for Wednesday.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: the meeting start time (in minutes since midnight) on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting time to lie within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Preference constraints (soft constraints):
# 1. Judith would like to avoid more meetings on Monday.
opt.add_soft(meeting_day != 0, weight=1, id="avoid_monday")

# 2. Judith would like to avoid Wednesday meetings before 12:00.
# If the meeting is on Wednesday, ideally it should not start before 12:00.
opt.add_soft(If(meeting_day == 2, meeting_start >= time_to_minutes("12:00"), True),
             weight=1, id="wed_after_noon")

# Function to add busy constraints for a given participant.
def add_busy_constraints(schedule):
    for day in allowed_days:
        intervals = schedule.get(day, [])
        for busy_start, busy_end in intervals:
            # If the meeting is scheduled on that day, then it must not overlap with the busy interval.
            opt.add(If(meeting_day == day,
                       Or(meeting_end <= busy_start, meeting_start >= busy_end),
                       True))

# Add busy constraints for Judith and Timothy.
add_busy_constraints(judith_busy)
add_busy_constraints(timothy_busy)

# Objective: schedule the meeting at the earliest availability.
# We'll minimize the overall time metric: day*1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration
    
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")