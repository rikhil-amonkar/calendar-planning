from z3 import Optimize, Int, And, Or, Implies

# Helpers
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Problem data
days = ["Monday", "Tuesday", "Wednesday"]
day_indices = {d: i for i, d in enumerate(days)}

work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Busy schedules per participant: (day, start_min, end_min)
Tyler_busy = [
    ("Tuesday",  to_minutes("09:00"), to_minutes("09:30")),
    ("Tuesday",  to_minutes("14:30"), to_minutes("15:00")),
    ("Wednesday",to_minutes("10:30"), to_minutes("11:00")),
    ("Wednesday",to_minutes("12:30"), to_minutes("13:00")),
    ("Wednesday",to_minutes("13:30"), to_minutes("14:00")),
    ("Wednesday",to_minutes("16:30"), to_minutes("17:00")),
]

Ruth_busy = [
    ("Monday",   to_minutes("09:00"), to_minutes("10:00")),
    ("Monday",   to_minutes("10:30"), to_minutes("12:00")),
    ("Monday",   to_minutes("12:30"), to_minutes("14:30")),
    ("Monday",   to_minutes("15:00"), to_minutes("16:00")),
    ("Monday",   to_minutes("16:30"), to_minutes("17:00")),
    ("Tuesday",  to_minutes("09:00"), to_minutes("17:00")),
    ("Wednesday",to_minutes("09:00"), to_minutes("17:00")),
]

participants_busy = {
    "Tyler": [(day_indices[d], s, e) for d, s, e in Tyler_busy],
    "Ruth":  [(day_indices[d], s, e) for d, s, e in Ruth_busy],
}

# Z3 variables
opt = Optimize()
day = Int("day")       # 0=Monday, 1=Tuesday, 2=Wednesday
start = Int("start")   # minutes from 00:00

# Derived end time
end = start + duration

# Domains
opt.add(And(day >= 0, day <= 2))
opt.add(And(start >= work_start, end <= work_end))

# No overlap with any participant's busy intervals on the selected day
for person, intervals in participants_busy.items():
    for d_idx, s, e in intervals:
        # If this day equals the busy interval's day, ensure no overlap
        # Non-overlap: end <= s or start >= e
        opt.add(Implies(day == d_idx, Or(end <= s, start >= e)))

# Preference:
# Tyler would like to avoid more meetings on Monday before 16:00
# Soft constraint: If Monday, prefer start >= 16:00
opt.add_soft(Implies(day == day_indices["Monday"], start >= to_minutes("16:00")), "10")

# Solve
if opt.check() != sat:
    raise RuntimeError("No solution found, but the problem guarantees existence.")

model = opt.model()
chosen_day = days[model[day].as_long()]
start_min = model[start].as_long()
end_min = start_min + duration

print("SOLUTION:")
print(f"Day: {chosen_day}")
print(f"Start Time: {fmt_minutes(start_min)}")
print(f"End Time: {fmt_minutes(end_min)}")