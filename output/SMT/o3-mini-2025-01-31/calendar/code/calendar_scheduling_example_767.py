from z3 import Optimize, Int, Or, If, sat

# Helper functions for converting times.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one-hour meeting
work_start = time_to_minutes("9:00")   # 9:00 AM
work_end   = time_to_minutes("17:00")   # 5:00 PM

# Allowed days: Monday = 0, Tuesday = 1, Wednesday = 2.
allowed_days = [0, 1, 2]

# Busy intervals for Martha.
# Monday: 16:00 to 17:00
# Tuesday: 15:00 to 15:30
# Wednesday: 10:00 to 11:00, 14:00 to 14:30
martha_busy = {
    0: [(time_to_minutes("16:00"), time_to_minutes("17:00"))],
    1: [(time_to_minutes("15:00"), time_to_minutes("15:30"))],
    2: [(time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30"))]
}

# Busy intervals for Beverly.
# Monday: 9:00 to 13:30, 14:00 to 17:00
# Tuesday: 9:00 to 17:00
# Wednesday: 9:30 to 15:30, 16:30 to 17:00
beverly_busy = {
    0: [(time_to_minutes("9:00"),  time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("17:00"))],
    1: [(time_to_minutes("9:00"),  time_to_minutes("17:00"))],
    2: [(time_to_minutes("9:30"),  time_to_minutes("15:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))]
}

# Create an optimizer.
opt = Optimize()

# Decision variables:
# meeting_day: integer representing the day (0: Monday, 1: Tuesday, 2: Wednesday)
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: meeting start time (in minutes since midnight) on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add busy interval constraints for a given participant's schedule.
def add_busy_constraints(schedule):
    for d in allowed_days:
        for busy_start, busy_end in schedule.get(d, []):
            # If the meeting is on day d, it must either finish before a busy interval starts
            # or start after the busy interval ends.
            opt.add(If(meeting_day == d,
                       Or(meeting_end <= busy_start, meeting_start >= busy_end),
                       True))

# Add busy constraints for Martha and Beverly.
add_busy_constraints(martha_busy)
add_busy_constraints(beverly_busy)

# Objective: minimize the overall meeting time metric: day * 1440 + meeting_start.
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