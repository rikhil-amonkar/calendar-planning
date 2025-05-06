from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert between "HH:MM" strings and minutes since midnight
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration
meeting_duration = 30  # half-hour meeting 
work_start = time_to_minutes("9:00")   # 9:00 AM
work_end   = time_to_minutes("17:00")   # 5:00 PM

# Allowed days: Monday=0, Tuesday=1, Wednesday=2.
allowed_days = [0, 1, 2]

# Larry's calendar is wide open, so no busy intervals for him.

# Samuel's busy intervals.
samuel_busy = {
    0: [  # Monday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"),  time_to_minutes("12:00")),
        (time_to_minutes("14:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00"))
    ]
}

# Create the Z3 optimizer.
opt = Optimize()

# Decision variable for meeting day (0: Monday, 1: Tuesday, 2: Wednesday).
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# Decision variable for the meeting start time (in minutes from midnight).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Add busy schedule constraints for Samuel.
def add_busy_constraints(schedule):
    for d in allowed_days:
        intervals = schedule.get(d, [])
        for b_start, b_end in intervals:
            # For day d, meeting must not overlap a busy interval.
            opt.add(If(meeting_day == d,
                       Or(meeting_end <= b_start, meeting_start >= b_end),
                       True))
                       
add_busy_constraints(samuel_busy)

# Preferences:
# Larry would rather not meet on Wednesday (day 2).
opt.add_soft(meeting_day != 2, weight=1, id="larry_avoids_wed")
# Samuel would like to avoid more meetings on Tuesday (day 1).
opt.add_soft(meeting_day != 1, weight=1, id="samuel_avoids_tue")

# To meet at the earliest availability, minimize overall time metric (day * 1440 + meeting_start).
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration

    # Map day numbers to names.
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")