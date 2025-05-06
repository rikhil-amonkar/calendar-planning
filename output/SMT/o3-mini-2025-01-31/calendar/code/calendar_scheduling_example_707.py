from z3 import Optimize, Int, Or, Implies, sat

# Helper functions to convert times.
def time_to_minutes(t):
    # Converts a time "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # Half-hour meeting.
work_start = time_to_minutes("9:00")   # 540 minutes.
work_end   = time_to_minutes("17:00")   # 1020 minutes.

# Days encoding:
# 0 -> Monday, 1 -> Tuesday, 2 -> Wednesday
# However, Ryan cannot meet on Wednesday, so allowed days are Monday and Tuesday.
allowed_days = [0, 1]

# Busy intervals (in minutes) for Ryan.
# Monday busy:
ryan_monday = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("11:00"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]
# Tuesday busy:
ryan_tuesday = [
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]
# (Wednesday busy omitted; Ryan cannot meet on Wednesday.)
      
# Busy intervals for Adam.
# Monday busy:
adam_monday = [
    (time_to_minutes("9:00"),  time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]
# Tuesday busy:
adam_tuesday = [
    (time_to_minutes("9:00"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]
# Wednesday busy not needed because Ryan cannot meet on Wednesday.

# Additional constraint:
# Adam would like to avoid more meetings on Monday before 14:30.
adam_monday_preference = time_to_minutes("14:30")  # 870 minutes.

# Create our optimizer.
opt = Optimize()

# Decision variables: meeting_day and meeting_start
meeting_day = Int("meeting_day")
# Only allow Monday (0) or Tuesday (1)
opt.add(Or(meeting_day == allowed_days[0], meeting_day == allowed_days[1]))

meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Add Adam's preference for Monday: if the meeting is on Monday, then start no earlier than 14:30.
opt.add(Implies(meeting_day == 0, meeting_start >= adam_monday_preference))

# Function to add non-overlap constraints for a busy interval on a given day.
def add_busy_constraints(busy_intervals, day_val):
    for busy_start, busy_end in busy_intervals:
        # If meeting is scheduled on day_val, then it must not overlap the busy interval.
        opt.add(Implies(meeting_day == day_val, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Add busy constraints for Ryan.
add_busy_constraints(ryan_monday, 0)
add_busy_constraints(ryan_tuesday, 1)

# Add busy constraints for Adam.
add_busy_constraints(adam_monday, 0)
add_busy_constraints(adam_tuesday, 1)

# To pick the earliest available meeting, we minimize a compound objective.
# We prioritize Monday over Tuesday by weighting the day, then the start time.
opt.minimize(meeting_day * 10000 + meeting_start)

# Check for a valid meeting time.
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