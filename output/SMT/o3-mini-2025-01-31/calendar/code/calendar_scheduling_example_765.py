from z3 import Optimize, Int, Or, If, sat

# Helper functions for converting times.
def time_to_minutes(t):
    # Converts a "HH:MM" time string into minutes past midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes past midnight into a "HH:MM" time string.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # half-hour meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM
work_end   = time_to_minutes("17:00")   # 5:00 PM

# Allowed meeting days: Monday=0, Tuesday=1, Wednesday=2.
allowed_days = [0, 1, 2]

# Busy intervals for Joshua.
# Monday: 15:00 to 15:30.
# Tuesday: 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:00.
# Wednesday: No meetings.
joshua_busy = {
    0: [(time_to_minutes("15:00"), time_to_minutes("15:30"))],
    1: [
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ],
    2: []  # No busy intervals on Wednesday.
}

# Busy intervals for Joyce.
# Monday: 9:00-9:30, 10:00-11:00, 11:30-12:30, 13:00-15:00, 15:30-17:00.
# Tuesday: 9:00-17:00 (full day busy).
# Wednesday: 9:00-9:30, 10:00-11:00, 12:30-15:30, 16:00-16:30.
joyce_busy = {
    0: [
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("17:00"))
    ],
    1: [
        (time_to_minutes("9:00"),  time_to_minutes("17:00"))
    ],
    2: [
        (time_to_minutes("9:00"),  time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("12:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Create the Z3 optimizer instance.
opt = Optimize()

# Decision Variables:
# meeting_day: integer representing the day (Monday=0, Tuesday=1, Wednesday=2).
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: meeting start time (in minutes since midnight) on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Hard constraints: meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add busy time constraints.
def add_busy_constraints(schedule):
    # For each allowed day, ensure that if the meeting is on that day,
    # it does not overlap with any busy interval.
    for d in allowed_days:
        intervals = schedule.get(d, [])
        for b_start, b_end in intervals:
            opt.add(If(meeting_day == d,
                       Or(meeting_end <= b_start, meeting_start >= b_end),
                       True))

# Add busy constraints for both Joshua and Joyce.
add_busy_constraints(joshua_busy)
add_busy_constraints(joyce_busy)

# Joyce's preference: she would rather not meet on Monday before 12:00.
# We add this as a soft constraint; if meeting is on Monday, then ideally meeting_start >= 12:00.
no_early_monday = If(meeting_day == 0, meeting_start >= time_to_minutes("12:00"), True)
opt.add_soft(no_early_monday, weight=1, id="no_monday_before_12")

# We also set an objective to choose the earliest available meeting time;
# we define an overall metric as day*1440 + meeting_start (prioritizing earlier days and times).
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration

    # Map day integers to day names.
    day_mapping = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_mapping[chosen_day])
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")