from z3 import Optimize

# Helper functions to convert between time and minutes.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30 minutes meeting.
work_start = time_to_minutes("9:00")   # 540 minutes.
work_end   = time_to_minutes("17:00")  # 1020 minutes.

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Define busy intervals for Nancy and Jose per day.
# Each busy interval is a tuple (start, end) in minutes.
busy = {
    # Nancy's busy intervals.
    'Nancy': {
        0: [   # Monday
            (time_to_minutes("10:00"), time_to_minutes("10:30")),
            (time_to_minutes("11:30"), time_to_minutes("12:30")),
            (time_to_minutes("13:30"), time_to_minutes("14:00")),
            (time_to_minutes("14:30"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("17:00"))
        ],
        1: [   # Tuesday
            (time_to_minutes("9:30"), time_to_minutes("10:30")),
            (time_to_minutes("11:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("15:30"), time_to_minutes("16:00"))
        ],
        2: [   # Wednesday
            (time_to_minutes("10:00"), time_to_minutes("11:30")),
            (time_to_minutes("13:30"), time_to_minutes("16:00"))
        ]
    },
    # Jose's busy intervals.
    'Jose': {
        0: [   # Monday
            (time_to_minutes("9:00"), time_to_minutes("17:00"))
        ],
        1: [   # Tuesday
            (time_to_minutes("9:00"), time_to_minutes("17:00"))
        ],
        2: [   # Wednesday
            (time_to_minutes("9:00"), time_to_minutes("9:30")),
            (time_to_minutes("10:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:30"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("17:00"))
        ]
    }
}

# Create an Optimize object to allow minimization.
opt = Optimize()

# Define variables:
# day: represents the day (0 for Monday, 1 for Tuesday, 2 for Wednesday).
# meeting_start: start time (in minutes) of the meeting.
day = opt.int_val(0)  # dummy initialization; we will constrain it below.
meeting_day = opt.int_const("day")
opt.add(meeting_day >= 0, meeting_day <= 2)  # day ∈ {0, 1, 2}

meeting_start = opt.int_const("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: meeting must be within the work hours.
opt.add(meeting_start >= work_start)
opt.add(meeting_end <= work_end)

# For each participant and each day, if the meeting is scheduled on that day then
# the meeting must not overlap any busy interval.
for person in busy:
    for d in busy[person]:
        for (busy_start, busy_end) in busy[person][d]:
            # Add: If meeting_day is d then either the meeting ends before the busy period starts or
            # it starts after the busy period ends.
            opt.add(   (meeting_day == d) 
                     >> ( (meeting_end <= busy_start) | (meeting_start >= busy_end) ) )

# The group would like to meet at their earliest availability.
# We use the Optimize object to minimize the meeting start time.
opt.minimize(meeting_start)

if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration

    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[chosen_day]
    print("A possible meeting time (at earliest availability):")
    print(f"Day:   {day_str}")
    print(f"Start: {minutes_to_time(start_time)}")
    print(f"End:   {minutes_to_time(end_time)}")
else:
    print("No valid meeting time could be found.")