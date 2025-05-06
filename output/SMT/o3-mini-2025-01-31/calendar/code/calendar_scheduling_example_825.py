from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert between time strings and minutes.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one-hour meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM
work_end   = time_to_minutes("17:00")   # 5:00 PM

# Allowed days as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# The task permits meetings on Monday, Tuesday, Wednesday or Thursday,
# but Philip cannot meet on Wednesday.
allowed_days = [0, 1, 2, 3]
# Add a hard constraint to exclude Wednesday (day 2) for Philip.
# (Alternatively, we could define allowed_days = [0,1,3], but we'll add a constraint.)
exclude_wednesday = (lambda d: d != 2)

# Busy intervals for Laura (per day):
# Monday:
#    10:30-11:00, 12:30-13:00, 14:30-15:30, 16:00-17:00
# Tuesday:
#    9:30-10:00, 11:00-11:30, 13:00-13:30, 14:30-15:00, 16:00-17:00
# Wednesday:
#    (Not needed because Philip is not meeting on Wednesday for our solution, 
#     but here are intervals anyway: 11:30-12:00, 12:30-13:30, 15:00-? -- see task: 
#     "Laura is busy on Wednesday during 11:30 to 12:00" seems to be omitted? Actually, 
#     task lists Tuesday and Thursday for Laura; re-read task:)
# Re-check the task details for Laura:
# "Laura is busy on Monday during 10:30 to 11:00, 12:30 to 13:00, 14:30 to 15:30, 16:00 to 17:00,
#  Tuesday during 9:30 to 10:00, 11:00 to 11:30, 13:00 to 13:30, 14:30 to 15:00, 16:00 to 17:00,
#  Wednesday during 11:30 to 12:00, 12:30 to 13:30, 15:30 to 16:30,
#  Thursday during 10:30 to 11:00, 12:00 to 13:30, 15:00 to 15:30, 16:00 to 16:30;"
laura_busy = {
    0: [  # Monday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:30"),  time_to_minutes("10:00")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ],
    3: [  # Thursday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("13:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Busy intervals for Philip:
# Monday:
#    9:00-17:00 (fully booked),
# Tuesday:
#    9:00-11:00, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-16:30,
# Wednesday:
#    9:00-10:00, 11:00-12:00, 12:30-16:00, 16:30-17:00, (but he cannot meet this day)
# Thursday:
#    9:00-10:30, 11:00-12:30, 13:00-17:00.
philip_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:30"))
    ],
    2: [  # Wednesday (Philip cannot meet on this day)
        (time_to_minutes("9:00"),  time_to_minutes("10:00")),
        (time_to_minutes("11:00"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:00"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("17:00"))
    ]
}

# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# meeting_day: integer representing the day (Monday=0, Tuesday=1, Wednesday=2, Thursday=3).
meeting_day = Int("meeting_day")
# We allow meeting_day to be one of the permitted days.
opt.add(Or([meeting_day == d for d in allowed_days]))
# Enforce Philip's requirement: he cannot meet on Wednesday.
opt.add(meeting_day != 2)

# meeting_start: start time (in minutes from midnight) on the selected day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add busy interval constraints for a participant's schedule.
def add_busy_constraints(schedule):
    for d in allowed_days:
        intervals = schedule.get(d, [])
        for b_start, b_end in intervals:
            # If the meeting is on day d, it must either finish before a busy interval
            # starts or start after that busy interval ends.
            opt.add(If(meeting_day == d,
                       Or(meeting_end <= b_start, meeting_start >= b_end),
                       True))
            
# Add busy constraints for both Laura and Philip.
add_busy_constraints(laura_busy)
add_busy_constraints(philip_busy)

# Objective: Schedule the meeting at the earliest available time.
# We use an overall time measure: day * 1440 + meeting_start, to prioritize earlier days and times.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration

    # Map day integers to day names.
    day_names = {0: "Monday", 1: "Tuesday", 3: "Thursday"}
    print("A possible meeting time:")
    print("Day:   ", day_names.get(chosen_day, "Unknown"))
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")