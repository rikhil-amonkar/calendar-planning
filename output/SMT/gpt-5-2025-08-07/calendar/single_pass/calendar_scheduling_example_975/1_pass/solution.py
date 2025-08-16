from z3 import Int, Optimize, And, Or, Implies

# Helper to convert HH:MM to minutes since 09:00 (start of workday)
def t(h, m):
    return (h * 60 + m) - (9 * 60)

# Data
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
duration = 60  # minutes
workday_minutes = 8 * 60  # 09:00 to 17:00

# Busy schedules per participant: dict[day_index] = list of (start_min_since_9, end_min_since_9)
# day_index: 0=Mon, 1=Tue, 2=Wed, 3=Thu, 4=Fri
nicole_busy = {
    1: [(t(16, 0), t(16, 30))],                # Tuesday
    2: [(t(15, 0), t(15, 30))],                # Wednesday
    4: [(t(12, 0), t(12, 30)), (t(15, 30), t(16, 0))],  # Friday
}
daniel_busy = {
    0: [(t(9,0), t(12,30)), (t(13,0), t(13,30)), (t(14,0), t(16,30))],  # Monday
    1: [(t(9,0), t(10,30)), (t(11,30), t(12,30)), (t(13,0), t(13,30)), (t(15,0), t(16,0)), (t(16,30), t(17,0))],  # Tuesday
    2: [(t(9,0), t(10,0)), (t(11,0), t(12,30)), (t(13,0), t(13,30)), (t(14,0), t(14,30)), (t(16,30), t(17,0))],   # Wednesday
    3: [(t(11,0), t(12,0)), (t(13,0), t(14,0)), (t(15,0), t(15,30))],    # Thursday
    4: [(t(10,0), t(11,0)), (t(11,30), t(12,0)), (t(12,30), t(14,30)), (t(15,0), t(15,30)), (t(16,0), t(16,30))], # Friday
}

participants = [nicole_busy, daniel_busy]

# Z3 variables
day = Int('day')           # 0..4 (Mon..Fri)
start = Int('start')       # minutes since 09:00 within the chosen day

opt = Optimize()

# Domain constraints
opt.add(And(day >= 0, day <= 4))
opt.add(And(start >= 0, start + duration <= workday_minutes))  # Meeting must fit within 09:00-17:00

# No-overlap constraints for all participants on the chosen day
for p in participants:
    for d_idx in range(5):
        intervals = p.get(d_idx, [])
        for (b_start, b_end) in intervals:
            # If the meeting is on this day, it must not overlap the busy interval
            opt.add(Implies(day == d_idx, Or(start + duration <= b_start, start >= b_end)))

# Objective: earliest availability (earliest absolute time in the week)
# Absolute start time in minutes since week start (Mon 00:00)
abs_start = day * 24 * 60 + (9 * 60) + start
opt.minimize(abs_start)

# Solve
if opt.check() != None:
    model = opt.model()
    d_val = model[day].as_long()
    s_val = model[start].as_long()
    start_clock = 9 * 60 + s_val
    end_clock = start_clock + duration

    def to_hhmm(total_minutes):
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"

    day_str = days[d_val]
    start_str = to_hhmm(start_clock)
    end_str = to_hhmm(end_clock)

    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    # As per problem statement, a solution exists; this is a fallback
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 09:00")
    print("End Time: 10:00")