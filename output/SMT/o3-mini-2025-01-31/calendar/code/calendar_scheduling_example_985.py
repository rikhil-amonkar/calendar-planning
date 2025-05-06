from z3 import Optimize, Int, Or, If, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Converts a string "HH:MM" to the number of minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight back to a "HH:MM" string.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one-hour meeting.
work_start = time_to_minutes("9:00")    # 9:00 AM
work_end   = time_to_minutes("17:00")    # 5:00 PM

# Allowed days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3, Friday=4.
allowed_days = [0, 1, 2, 3, 4]

# Busy intervals for Diane.
diane_busy = {
    0: [  # Monday
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ],
    4: [  # Friday
        (time_to_minutes("9:30"), time_to_minutes("11:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]
}

# Busy intervals for Matthew.
matthew_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    3: [  # Thursday
        (time_to_minutes("9:00"), time_to_minutes("16:00"))
    ],
    4: [  # Friday
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ]
}

# Create a Z3 Optimize solver.
opt = Optimize()

# Decision variables.
# meeting_day: integer representing the day (Monday=0, Tuesday=1, Wednesday=2, Thursday=3, Friday=4)
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: meeting start time in minutes since midnight on the selected day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within regular work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Matthew's preference: if meeting is on Wednesday (day 2), do not meet before 12:30.
opt.add(If(meeting_day == 2, meeting_start >= time_to_minutes("12:30"), True))

# Function to add busy constraints for a participant.
def add_busy_constraints(schedule):
    for day, intervals in schedule.items():
        for b_start, b_end in intervals:
            # If the meeting is on a specific day, then it must not overlap with any busy interval.
            opt.add(If(meeting_day == day,
                       Or(meeting_end <= b_start, meeting_start >= b_end),
                       True))

# Add busy constraints for both Diane and Matthew.
add_busy_constraints(diane_busy)
add_busy_constraints(matthew_busy)

# Objective: schedule the meeting at the earliest available time.
# Define "overall_time" to be a combined measure of day and start time.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve and print the solution.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration

    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")