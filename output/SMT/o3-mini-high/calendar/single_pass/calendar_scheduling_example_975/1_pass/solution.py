from z3 import Optimize, Int, Or, Implies

# Define our variables:
# meeting_day: 1=Monday, 2=Tuesday, 3=Wednesday, 4=Thursday, 5=Friday
# meeting_start: start time in minutes from midnight (we use minutes so that 9:00 is 540)
meeting_day = Int("meeting_day")
meeting_start = Int("meeting_start")
meeting_end = meeting_start + 60  # Meeting duration is 60 minutes

opt = Optimize()

# Constraint: meeting day is one of Monday to Friday
opt.add(meeting_day >= 1, meeting_day <= 5)
# Constraint: meeting must fall within work hours (9:00 to 17:00)
# Latest meeting start is 16:00 (i.e., 960 minutes) so that meeting_end = 1020 (17:00)
opt.add(meeting_start >= 9 * 60, meeting_start <= 16 * 60)

# Busy time intervals (in minutes) for each participant.
# Each busy interval is a tuple: (day, busy_start, busy_end)
busy_intervals = [
    # Nicole's busy intervals
    (2, 16 * 60, 16 * 60 + 30),      # Tuesday 16:00-16:30
    (3, 15 * 60, 15 * 60 + 30),        # Wednesday 15:00-15:30
    (5, 12 * 60, 12 * 60 + 30),        # Friday 12:00-12:30
    (5, 15 * 60 + 30, 16 * 60),        # Friday 15:30-16:00

    # Daniel's busy intervals
    (1, 9 * 60, 12 * 60 + 30),         # Monday 9:00-12:30
    (1, 13 * 60, 13 * 60 + 30),        # Monday 13:00-13:30
    (1, 14 * 60, 16 * 60 + 30),        # Monday 14:00-16:30

    (2, 9 * 60, 10 * 60 + 30),         # Tuesday 9:00-10:30
    (2, 11 * 60 + 30, 12 * 60 + 30),    # Tuesday 11:30-12:30
    (2, 13 * 60, 13 * 60 + 30),        # Tuesday 13:00-13:30
    (2, 15 * 60, 16 * 60),             # Tuesday 15:00-16:00
    (2, 16 * 60 + 30, 17 * 60),        # Tuesday 16:30-17:00

    (3, 9 * 60, 10 * 60),              # Wednesday 9:00-10:00
    (3, 11 * 60, 12 * 60 + 30),        # Wednesday 11:00-12:30
    (3, 13 * 60, 13 * 60 + 30),        # Wednesday 13:00-13:30
    (3, 14 * 60, 14 * 60 + 30),        # Wednesday 14:00-14:30
    (3, 16 * 60 + 30, 17 * 60),        # Wednesday 16:30-17:00

    (4, 11 * 60, 12 * 60),             # Thursday 11:00-12:00
    (4, 13 * 60, 14 * 60),             # Thursday 13:00-14:00
    (4, 15 * 60, 15 * 60 + 30),        # Thursday 15:00-15:30

    (5, 10 * 60, 11 * 60),             # Friday 10:00-11:00
    (5, 11 * 60 + 30, 12 * 60),        # Friday 11:30-12:00
    (5, 12 * 60 + 30, 14 * 60 + 30),    # Friday 12:30-14:30
    (5, 15 * 60, 15 * 60 + 30),        # Friday 15:00-15:30
    (5, 16 * 60, 16 * 60 + 30)         # Friday 16:00-16:30
]

# For each busy interval, if the meeting is on that same day,
# then the meeting should finish before the busy interval starts or start after it ends.
for (b_day, b_start, b_end) in busy_intervals:
    opt.add(Implies(meeting_day == b_day,
                    Or(meeting_end <= b_start, meeting_start >= b_end)))

# We want the meeting at the earliest possible time.
# Use optimization to minimize the meeting day, and then the start time.
opt.minimize(meeting_day)
opt.minimize(meeting_start)

# Check for a solution
if opt.check() == 'sat':
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + 60  # Meeting duration is 60 minutes

    # Convert minutes into HH:MM format
    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"
    
    day_map = {
        1: "Monday",
        2: "Tuesday",
        3: "Wednesday",
        4: "Thursday",
        5: "Friday"
    }
    
    result_day = day_map[chosen_day]
    result_start = minutes_to_time(chosen_start)
    result_end = minutes_to_time(chosen_end)
    
    # The output needs to be a string that starts with 'SOLUTION:' followed by three lines.
    output = f"SOLUTION:\nDay: {result_day}\nStart Time: {result_start}\nEnd Time: {result_end}"
    print(output)
else:
    print("No solution found.")