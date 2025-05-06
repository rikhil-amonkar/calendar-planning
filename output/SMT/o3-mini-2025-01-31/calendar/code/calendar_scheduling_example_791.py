from z3 import Optimize, Int, Or, If, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Converts time string "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight to time string "HH:MM".
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # half an hour meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM -> 540 minutes.
work_end   = time_to_minutes("17:00")   # 5:00 PM -> 1020 minutes.

# Allowed days: Monday = 0, Tuesday = 1, Wednesday = 2.
allowed_days = [0, 1, 2]

# Busy intervals for Nicole.
nicole_busy = {
    0: [  # Monday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:30"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("11:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:30"))
    ],
    2: [  # Wednesday
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("12:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]
}

# Busy intervals for Ruth.
ruth_busy = {
    0: [  # Monday: Busy all day.
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday: Busy all day.
        (time_to_minutes("9:00"), time_to_minutes("17:00"))
    ],
    2: [  # Wednesday
        (time_to_minutes("9:00"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables.
# meeting_day: 0 for Monday, 1 for Tuesday, 2 for Wednesday.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: start time in minutes since midnight on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting time to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Additional constraint: if meeting is on Wednesday (day 2), Ruth does not want to meet after 13:30.
opt.add(If(meeting_day == 2, meeting_end <= time_to_minutes("13:30"), True))

# Function to add busy constraints for a given participant on a specific day.
def add_daily_busy(day_busy):
    for day, intervals in day_busy.items():
        for b_start, b_end in intervals:
            # If the meeting is scheduled on that day, it must not overlap with the busy interval.
            opt.add(If(meeting_day == day, Or(meeting_end <= b_start, meeting_start >= b_end), True))

# Add busy constraints for both participants.
add_daily_busy(nicole_busy)
add_daily_busy(ruth_busy)

# Objective: choose the earliest available meeting time using an overall metric.
# Overall time = meeting_day * 1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")