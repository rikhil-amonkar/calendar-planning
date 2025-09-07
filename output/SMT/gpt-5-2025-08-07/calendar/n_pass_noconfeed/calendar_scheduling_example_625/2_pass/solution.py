import z3

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60   # 09:00 in minutes from midnight
WORK_END   = 17 * 60  # 17:00 in minutes from midnight
DAY_START_MINUTE = 0
DAY_END_MINUTE = (WORK_END - WORK_START)  # 480 minutes (8 hours)

# Create optimizer
opt = z3.Optimize()

# Decision variables
day = z3.Int('day')      # 0 = Monday, 1 = Tuesday
start = z3.Int('start')  # minutes from 09:00 within the chosen day

# Hard constraints: day domain and within working hours
opt.add(z3.Or(day == 0, day == 1))
opt.add(z3.And(start >= DAY_START_MINUTE, start + DURATION <= DAY_END_MINUTE))
# Schedule in 30-minute increments
opt.add(start % 30 == 0)

# Helper to ensure no overlap with a busy interval [b_start, b_end)
def no_overlap(b_start, b_end):
    return z3.Or(start + DURATION <= b_start, start >= b_end)

# Harold's busy times relative to 09:00 for each day
monday_busy = [
    (0, 60),    # 09:00 - 10:00
    (90, 480),  # 10:30 - 17:00
]
tuesday_busy = [
    (0, 30),    # 09:00 - 09:30
    (90, 150),  # 10:30 - 11:30
    (210, 270), # 12:30 - 13:30
    (330, 390), # 14:30 - 15:30
    (420, 480), # 16:00 - 17:00
]

# Enforce Harold's availability
opt.add(z3.Implies(day == 0, z3.And(*[no_overlap(s, e) for (s, e) in monday_busy])))
opt.add(z3.Implies(day == 1, z3.And(*[no_overlap(s, e) for (s, e) in tuesday_busy])))

# Preferences (soft constraints):
# 1) Prefer Tuesday over Monday
opt.add_soft(day == 1, weight=10)
# 2) Prefer on Tuesday at or after 14:30 (avoid Tuesday before 14:30)
opt.add_soft(z3.Implies(day == 1, start >= 330), weight=5)

# Tie-breaker: among equally preferred options, choose earliest time
opt.minimize(start)

if opt.check() == z3.sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start].as_long()

    # Convert to absolute minutes from midnight for formatting
    abs_start = WORK_START + s
    abs_end = abs_start + DURATION

    def fmt(mm):
        h = mm // 60
        mi = mm % 60
        return f"{h:02d}:{mi:02d}"

    day_name = ["Monday", "Tuesday"][d]
    print(f"{day_name} {{{fmt(abs_start)}:{fmt(abs_end)}}}")
else:
    print("No feasible meeting time found.")