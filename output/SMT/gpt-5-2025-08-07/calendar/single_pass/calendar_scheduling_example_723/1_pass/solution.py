from z3 import Int, Optimize, And, Or, Implies

# Helper to parse "HH:MM" into minutes since 00:00
def parse_time(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Convert "HH:MM" into minutes since 09:00 (start of work window)
def since_9(t):
    return parse_time(t) - 9 * 60

# Busy schedules per person per day
# Days: 0=Monday, 1=Tuesday, 2=Wednesday
arthur_busy = {
    0: [("11:00", "11:30"), ("13:30", "14:00"), ("15:00", "15:30")],
    1: [("13:00", "13:30"), ("16:00", "16:30")],
    2: [("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
        ("14:00", "14:30"), ("16:00", "16:30")]
}

michael_busy = {
    0: [("09:00", "12:00"), ("12:30", "13:00"), ("14:00", "14:30"), ("15:00", "17:00")],
    1: [("09:30", "11:30"), ("12:00", "13:30"), ("14:00", "15:30")],
    2: [("10:00", "12:30"), ("13:00", "13:30")]
}

# Convert busy schedules to minutes since 09:00 for each day
def convert_busy(busy):
    conv = {}
    for d, intervals in busy.items():
        conv[d] = [(since_9(s), since_9(e)) for (s, e) in intervals]
    return conv

arthur_busy_mins = convert_busy(arthur_busy)
michael_busy_mins = convert_busy(michael_busy)

# Z3 variables
day = Int("day")      # 0=Mon,1=Tue,2=Wed
start = Int("start")  # minutes since 09:00
dur = 30
end = start + dur

opt = Optimize()

# Domain constraints
opt.add(day >= 0, day <= 2)
opt.add(start >= 0, end <= 8 * 60)  # within 09:00-17:00
opt.add(start % 30 == 0)            # half-hour granularity

# Arthur cannot meet on Tuesday
opt.add(day != 1)

# Non-overlap constraints for each participant
def add_non_overlap(busy_map):
    for d, intervals in busy_map.items():
        for (s, e) in intervals:
            # If meeting is on day d, it must not overlap [s, e)
            opt.add(Implies(day == d, Or(end <= s, start >= e)))

add_non_overlap(arthur_busy_mins)
add_non_overlap(michael_busy_mins)

# Objective: earliest availability (minimize absolute minutes from Monday 09:00)
opt.minimize(day * (8 * 60) + start)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found, but a solution was expected.")

m = opt.model()
d_val = m[day].as_long()
s_val = m[start].as_long()
e_val = s_val + dur

days = ["Monday", "Tuesday", "Wednesday"]

# Convert back to HH:MM (24-hour), adding 09:00 offset
def to_hhmm(mins_since_9):
    total = 9 * 60 + mins_since_9
    h = total // 60
    m_ = total % 60
    return f"{h:02d}:{m_:02d}"

day_str = days[d_val]
start_str = to_hhmm(s_val)
end_str = to_hhmm(e_val)

print("SOLUTION:")
print(f"Day: {day_str}")
print(f"Start Time: {start_str}")
print(f"End Time: {end_str}")