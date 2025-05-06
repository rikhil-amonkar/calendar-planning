from z3 import Optimize, Int, Or, If, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Converts "HH:MM" format to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight to "HH:MM" format.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 60  # one hour meeting
work_start = time_to_minutes("9:00")    # 9:00 AM
work_end   = time_to_minutes("17:00")    # 5:00 PM

# Allowed days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
allowed_days = [0, 1, 2, 3]

# Busy intervals for Carl.
carl_busy = {
    0: [ (time_to_minutes("11:00"), time_to_minutes("11:30")) ],
    1: [ (time_to_minutes("14:30"), time_to_minutes("15:00")) ],
    2: [ (time_to_minutes("10:00"), time_to_minutes("11:30")),
         (time_to_minutes("13:00"), time_to_minutes("13:30")) ],
    3: [ (time_to_minutes("13:30"), time_to_minutes("14:00")),
         (time_to_minutes("16:00"), time_to_minutes("16:30")) ]
}

# Busy intervals for Margaret.
margaret_busy = {
    0: [ (time_to_minutes("9:00"), time_to_minutes("10:30")),
         (time_to_minutes("11:00"), time_to_minutes("17:00")) ],
    1: [ (time_to_minutes("9:30"), time_to_minutes("12:00")),
         (time_to_minutes("13:30"), time_to_minutes("14:00")),
         (time_to_minutes("15:30"), time_to_minutes("17:00")) ],
    2: [ (time_to_minutes("9:30"), time_to_minutes("12:00")),
         (time_to_minutes("12:30"), time_to_minutes("13:00")),
         (time_to_minutes("13:30"), time_to_minutes("14:30")),
         (time_to_minutes("15:00"), time_to_minutes("17:00")) ],
    3: [ (time_to_minutes("10:00"), time_to_minutes("12:00")),
         (time_to_minutes("12:30"), time_to_minutes("14:00")),
         (time_to_minutes("14:30"), time_to_minutes("17:00")) ]
}

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables.
# meeting_day: 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start is in minutes since midnight on that day.
meeting_start = Int("meeting_start")
meeting_end   = meeting_start + meeting_duration

# Constrain meeting time to fall within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Carl prefers to avoid meetings on Thursday.
opt.add_soft(meeting_day != 3, weight=1)

# Define a helper to add busy time constraints for a given day.
def add_busy_constraints_for_day(day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # If the meeting is scheduled on the specified day, it should not overlap the busy interval.
        opt.add(If(meeting_day == day,
                   Or(meeting_end <= b_start, meeting_start >= b_end),
                   True))

# Add busy constraints for Carl.
for day, intervals in carl_busy.items():
    add_busy_constraints_for_day(day, intervals)

# Add busy constraints for Margaret.
for day, intervals in margaret_busy.items():
    add_busy_constraints_for_day(day, intervals)

# Objective: schedule as early as possible.
# We'll use an overall time metric: day * 1440 + meeting_start.
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Check for a solution and display it.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    
    # Map day number to day name.
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")