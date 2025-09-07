from z3 import Optimize, Int, Or, Implies, And, sat

# Meeting parameters
meeting_duration = 30
work_start = 0       # 9:00 is 0 minutes offset
work_end = 480       # 17:00 is 480 minutes offset

# Define day constants
MON, TUE, WED, THU = 0, 1, 2, 3
day_names = {MON: "Monday", TUE: "Tuesday", WED: "Wednesday", THU: "Thursday"}

# James's busy intervals (in minutes offset from 9:00)
# Each tuple is (busy_start, busy_end)
busy_schedules = {
    MON: [(0, 30), (90, 120), (210, 240), (330, 390), (450, 480)],
    TUE: [(0, 120), (150, 180), (210, 450), (420, 480)],
    WED: [(60, 120), (180, 240), (270, 420)],
    THU: [(30, 150), (180, 210), (240, 270), (300, 330), (450, 480)]
}

opt = Optimize()

# Decision variables:
# "day" must be one of the allowed days;
# "start" is the meeting start time (in minutes after 9:00).
day = Int("day")
start = Int("start")

# Allowed days: Monday, Tuesday, Wednesday, Thursday
opt.add(Or(day == MON, day == TUE, day == WED, day == THU))

# The meeting must start no earlier than 9:00 and finish by 17:00.
opt.add(start >= work_start, start + meeting_duration <= work_end)

# Cheryl’s preference: she would rather not meet on Wednesday.
opt.add(day != WED)

# For each day we add constraints so that if that day is chosen, the meeting does not overlap any busy interval.
for d, intervals in busy_schedules.items():
    # For each busy interval, the meeting must either finish before it starts
    # or must start after it ends.
    no_overlap = []
    for (b_start, b_end) in intervals:
        no_overlap.append(Or(start + meeting_duration <= b_start, start >= b_end))
    opt.add(Implies(day == d, And(*no_overlap)))

# We want the earliest possible meeting time.
# That is, we minimize first the day (with Monday = 0, Tuesday = 1, and Thursday = 3)
# and then minimize the start time.
opt.minimize(day)
opt.minimize(start)

# Check the optimization and print the model if one is found
if opt.check() == sat:
    m = opt.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    
    # Convert the time offset back to an actual time starting at 9:00.
    meeting_start_minutes = 9 * 60 + chosen_start
    meeting_end_minutes = meeting_start_minutes + meeting_duration
    
    # Helper function to convert minutes to HH:MM format.
    def to_HHMM(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    meeting_time = f"{to_HHMM(meeting_start_minutes)} - {to_HHMM(meeting_end_minutes)}"
    print(f"{day_names[chosen_day]} {meeting_time}")
else:
    print("No solution found.")