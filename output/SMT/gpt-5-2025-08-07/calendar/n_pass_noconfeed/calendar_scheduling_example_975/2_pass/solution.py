from z3 import Optimize, Int, Or, Implies, sat

# Helper to convert "HH:MM" to minutes since midnight
def t(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

# Days of the week considered
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Busy schedules (inclusive of start, exclusive of end)
# Times given as "HH:MM" strings for readability, converted to minutes below.
nicole_busy = {
    "Monday": [],
    "Tuesday": [("16:00", "16:30")],
    "Wednesday": [("15:00", "15:30")],
    "Thursday": [],
    "Friday": [("12:00", "12:30"), ("15:30", "16:00")],
}

daniel_busy = {
    "Monday": [("09:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")],
    "Tuesday": [("09:00", "10:30"), ("11:30", "12:30"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
    "Wednesday": [("09:00", "10:00"), ("11:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")],
    "Thursday": [("11:00", "12:00"), ("13:00", "14:00"), ("15:00", "15:30")],
    "Friday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")],
}

# Convert schedules to minutes
def convert_schedule(schedule):
    conv = {}
    for d in days:
        conv[d] = [(t(s), t(e)) for (s, e) in schedule.get(d, [])]
    return conv

nicole_busy_m = convert_schedule(nicole_busy)
daniel_busy_m = convert_schedule(daniel_busy)

# Z3 variables
day = Int("day")       # 0 = Monday, ..., 4 = Friday
start = Int("start")   # minutes since midnight
end = Int("end")

opt = Optimize()
opt.set("priority", "lex")  # Minimize day first, then start time

# Meeting duration and work hours
WORK_START = t("09:00")
WORK_END = t("17:00")
DURATION = 60

# Basic constraints
opt.add(day >= 0, day <= 4)
opt.add(end == start + DURATION)
opt.add(start >= WORK_START)
opt.add(end <= WORK_END)

# No-overlap constraints for each participant on the selected day
for d_idx, d_name in enumerate(days):
    # Nicole
    for (bs, be) in nicole_busy_m[d_name]:
        opt.add(Implies(day == d_idx, Or(end <= bs, start >= be)))
    # Daniel
    for (bs, be) in daniel_busy_m[d_name]:
        opt.add(Implies(day == d_idx, Or(end <= bs, start >= be)))

# Earliest availability: minimize day, then start
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    day_idx = model[day].as_long()
    s = model[start].as_long()
    e = model[end].as_long()

    def fmt(m):
        return f"{m // 60:02d}:{m % 60:02d}"

    day_name = days[day_idx]
    print(f"{day_name} {{{fmt(s)}:{fmt(e)}}}")
else:
    print("No feasible meeting time found.")