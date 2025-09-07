from z3 import Int, Optimize, If, Implies, Or, sat

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Meeting parameters
meeting_duration = 60  # in minutes

# Decision variables:
# day: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
# start: meeting start time in minutes from midnight.
day = Int('day')
start = Int('start')

opt = Optimize()

# Working hours: meeting must be between 9:00 and 17:00.
# Because the meeting lasts one hour, start must be in [9:00, 16:00]
opt.add(day >= 0, day <= 4)
opt.add(start >= 9 * 60, start <= 16 * 60)  # 9:00 is 540; 16:00 is 960.

# Busy intervals for Brian and Julia.
# Each tuple is (day, busy_start, busy_end) where times are in minutes from midnight.
busy_intervals = [
    # Brian's busy intervals
    (0, 9 * 60 + 30, 10 * 60),      # Monday: 9:30-10:00
    (0, 12 * 60 + 30, 14 * 60 + 30),  # Monday: 12:30-14:30
    (0, 15 * 60 + 30, 16 * 60),      # Monday: 15:30-16:00
    (1, 9 * 60, 9 * 60 + 30),        # Tuesday: 9:00-9:30
    (2, 12 * 60 + 30, 14 * 60),      # Wednesday: 12:30-14:00
    (2, 16 * 60 + 30, 17 * 60),      # Wednesday: 16:30-17:00
    (3, 11 * 60, 11 * 60 + 30),      # Thursday: 11:00-11:30
    (3, 13 * 60, 13 * 60 + 30),      # Thursday: 13:00-13:30
    (3, 16 * 60 + 30, 17 * 60),      # Thursday: 16:30-17:00
    (4, 9 * 60 + 30, 10 * 60),       # Friday: 9:30-10:00
    (4, 10 * 60 + 30, 11 * 60),      # Friday: 10:30-11:00
    (4, 13 * 60, 13 * 60 + 30),      # Friday: 13:00-13:30
    (4, 15 * 60, 16 * 60),           # Friday: 15:00-16:00
    (4, 16 * 60 + 30, 17 * 60),      # Friday: 16:30-17:00

    # Julia's busy intervals
    (0, 9 * 60, 10 * 60),           # Monday: 9:00-10:00
    (0, 11 * 60, 11 * 60 + 30),      # Monday: 11:00-11:30
    (0, 12 * 60 + 30, 13 * 60),      # Monday: 12:30-13:00
    (0, 15 * 60 + 30, 16 * 60),      # Monday: 15:30-16:00
    (1, 13 * 60, 14 * 60),           # Tuesday: 13:00-14:00
    (1, 16 * 60, 16 * 60 + 30),      # Tuesday: 16:00-16:30
    (2, 9 * 60, 11 * 60 + 30),       # Wednesday: 9:00-11:30
    (2, 12 * 60, 12 * 60 + 30),      # Wednesday: 12:00-12:30
    (2, 13 * 60, 17 * 60),           # Wednesday: 13:00-17:00
    (3, 9 * 60, 10 * 60 + 30),       # Thursday: 9:00-10:30
    (3, 11 * 60, 17 * 60),           # Thursday: 11:00-17:00
    (4, 9 * 60, 10 * 60),           # Friday: 9:00-10:00
    (4, 10 * 60 + 30, 11 * 60 + 30),  # Friday: 10:30-11:30
    (4, 12 * 60 + 30, 14 * 60),      # Friday: 12:30-14:00
    (4, 14 * 60 + 30, 15 * 60),      # Friday: 14:30-15:00
    (4, 15 * 60 + 30, 16 * 60)       # Friday: 15:30-16:00
]

# For each busy interval, if the meeting is scheduled on that day, ensure it does not overlap.
for busy_day, busy_start, busy_end in busy_intervals:
    opt.add(Implies(day == busy_day, Or(start + meeting_duration <= busy_start,
                                          start >= busy_end)))

# Soft constraint: Brian would like to avoid meetings on Monday (day 0) if possible.
penalty = If(day == 0, 1, 0)
opt.minimize(penalty)

# Also, schedule the meeting at the earliest availability (first by day, then by start time).
opt.minimize(day * 10000 + start)

if opt.check() == sat:
    model = opt.model()
    meeting_day_val = model[day].as_long()
    meeting_start_val = model[start].as_long()
    meeting_end_val = meeting_start_val + meeting_duration

    day_names = {
        0: "Monday",
        1: "Tuesday",
        2: "Wednesday",
        3: "Thursday",
        4: "Friday"
    }
    day_str = day_names[meeting_day_val]
    start_str = format_time(meeting_start_val)
    end_str = format_time(meeting_end_val)
    
    # Output in the format: Day {HH:MM:HH:MM}
    print(f"{day_str} {{{start_str}:{end_str}}}")
else:
    print("No solution found.")