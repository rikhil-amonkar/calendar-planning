from z3 import Optimize, Int, Or, Implies, And

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
# 'day' takes one of the allowed values: Monday, Tuesday, Wednesday, Thursday.
day = Int("day")
start = Int("start")  # start time (in minutes after 9:00)

# Allowed days: 0 (Mon), 1 (Tue), 2 (Wed), 3 (Thu)
opt.add(Or(day == MON, day == TUE, day == WED, day == THU))

# Meeting must finish by 17:00 (i.e., work_end) and cannot start before 9:00.
opt.add(start >= work_start, start + meeting_duration <= work_end)

# Cheryl's preference: she would rather not meet on Wednesday.
# Since a solution exists on other days, we impose this as a hard constraint.
opt.add(day != WED)

# For each day, if that day is chosen, ensure the meeting does not overlap any of James's busy intervals.
for d, intervals in busy_schedules.items():
    # For each busy interval, the meeting must finish before the busy period starts
    # or start after the busy period ends.
    no_overlap = []
    for (b_start, b_end) in intervals:
        no_overlap.append(Or(start + meeting_duration <= b_start, start >= b_end))
    opt.add(Implies(day == d, And(*no_overlap)))

# We want the earliest possible meeting time.
# That is, we minimize first the day (Monday is 0, then Tuesday, then Thursday)
# and then minimize the start time (earlier in the day).
h1 = opt.minimize(day)
h2 = opt.minimize(start)

if opt.check() == 'sat':
    m = opt.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    # Convert the time offset back to an actual time starting at 9:00
    meeting_start_minutes = 9 * 60 + chosen_start
    meeting_end_minutes = meeting_start_minutes + meeting_duration

    # Helper function to convert minutes to HH:MM format
    def to_HHMM(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    meeting_time = f"{to_HHMM(meeting_start_minutes)}:{to_HHMM(meeting_end_minutes)}"
    print(f"{day_names[chosen_day]} {meeting_time}")
else:
    print("No solution found.")