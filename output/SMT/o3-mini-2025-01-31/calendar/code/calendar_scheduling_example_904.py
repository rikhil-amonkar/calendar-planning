from z3 import Optimize, Int, Or, Implies, sat

# Helper functions to convert time strings.
def time_to_minutes(time_str):
    # Converts "HH:MM" into total minutes since midnight.
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(total_minutes):
    # Converts total minutes since midnight into "HH:MM" format.
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # Duration in minutes
work_start = time_to_minutes("9:00")    # 9:00 -> 540 minutes
work_end   = time_to_minutes("17:00")    # 17:00 -> 1020 minutes

# Decision variable for meeting day.
# We'll use: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3, Friday = 4.
meeting_day = Int("meeting_day")
# Allowed days are 0..4.
allowed_days = [0,1,2,3,4]
# Initially restrict meeting_day to one of the allowed values.
day_constraint = Or([meeting_day == d for d in allowed_days])

# Busy intervals for each participant are provided for each day.
# We will add constraints only for the day the meeting is scheduled.

# Daniel's busy intervals (per day):
daniel_busy = {
    0: [  # Monday
        (time_to_minutes("9:30"), time_to_minutes("10:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("11:00"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30"))
    ],
    3: [  # Thursday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    4: [  # Friday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Bradley's busy intervals (per day):
bradley_busy = {
    0: [  # Monday
        (time_to_minutes("9:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("15:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("11:00"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ],
    4: [  # Friday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ]
}

# Preferences:
# Daniel prefers not to meet on Wednesday (2) or Thursday (3).
# Bradley does not want to meet on Monday (0), or on Friday (4),
# and if meeting on Tuesday (1) then not before 12:00.
# For "prefer not" and "do not want", we treat them as hard constraints.

# According to Daniel's preference, meeting_day cannot be 2 or 3.
daniel_allowed_days = [0, 1, 4]  # Monday, Tuesday, Friday

# According to Bradley's preference, meeting_day cannot be 0 or 4.
# And on Tuesday, meeting must start at or after 12:00.
bradley_allowed_days = [1, 2, 3]  # Tuesday, Wednesday, Thursday

# The overall allowed meeting days must be in the intersection:
#   Intersection of Daniel's allowed days ([0,1,4]) and Bradley's allowed days ([1,2,3])
# This is simply: {1} since 1 is the only common day.
# Therefore, we must schedule the meeting on Tuesday.
opt = Optimize()
opt.add(day_constraint)
opt.add(meeting_day == 1)

# Also, Bradley prefers Tuesday meetings not to be before 12:00.
tuesday_noon = time_to_minutes("12:00")
opt.add(Implies(meeting_day == 1, 
                # meeting_start must be at or after 12:00.
                meeting_start >= tuesday_noon))

# Decision variable for meeting start time (minutes from midnight).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to fall within working hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to add busy interval constraints for a given day and participant.
def add_busy_constraints_for_day(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # When meeting is scheduled on the specific day, it must not overlap any busy interval.
        opt.add(Implies(meeting_day == day, Or(meeting_end <= b_start, meeting_start >= b_end)))

# Add busy constraints for Daniel on Tuesday.
add_busy_constraints_for_day(1, daniel_busy[1])
# Add busy constraints for Bradley on Tuesday.
add_busy_constraints_for_day(1, bradley_busy[1])

# Objective: minimize meeting start time, so that the meeting is as early as possible on Tuesday.
opt.minimize(meeting_start)

if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_names = {0:"Monday", 1:"Tuesday", 2:"Wednesday", 3:"Thursday", 4:"Friday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")