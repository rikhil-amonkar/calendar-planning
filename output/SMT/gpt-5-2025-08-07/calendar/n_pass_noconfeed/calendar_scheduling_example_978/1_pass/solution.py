from z3 import *

# Helper to convert HH:MM to minutes since midnight
def to_min(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

# Helper to format minutes since midnight as HH:MM
def min_to_str(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Work hours
work_start = to_min("09:00")
work_end   = to_min("17:00")
duration = 60  # 1 hour meeting

# Busy schedules per participant per day
# Represented as minutes since midnight [start, end)
Brian_busy = {
    0: [(to_min("09:30"), to_min("10:00")),
        (to_min("12:30"), to_min("14:30")),
        (to_min("15:30"), to_min("16:00"))],
    1: [(to_min("09:00"), to_min("09:30"))],
    2: [(to_min("12:30"), to_min("14:00")),
        (to_min("16:30"), to_min("17:00"))],
    3: [(to_min("11:00"), to_min("11:30")),
        (to_min("13:00"), to_min("13:30")),
        (to_min("16:30"), to_min("17:00"))],
    4: [(to_min("09:30"), to_min("10:00")),
        (to_min("10:30"), to_min("11:00")),
        (to_min("13:00"), to_min("13:30")),
        (to_min("15:00"), to_min("16:00")),
        (to_min("16:30"), to_min("17:00"))],
}

Julia_busy = {
    0: [(to_min("09:00"), to_min("10:00")),
        (to_min("11:00"), to_min("11:30")),
        (to_min("12:30"), to_min("13:00")),
        (to_min("15:30"), to_min("16:00"))],
    1: [(to_min("13:00"), to_min("14:00")),
        (to_min("16:00"), to_min("16:30"))],
    2: [(to_min("09:00"), to_min("11:30")),
        (to_min("12:00"), to_min("12:30")),
        (to_min("13:00"), to_min("17:00"))],
    3: [(to_min("09:00"), to_min("10:30")),
        (to_min("11:00"), to_min("17:00"))],
    4: [(to_min("09:00"), to_min("10:00")),
        (to_min("10:30"), to_min("11:30")),
        (to_min("12:30"), to_min("14:00")),
        (to_min("14:30"), to_min("15:00")),
        (to_min("15:30"), to_min("16:00"))],
}

# Z3 variables
day = Int("day")       # 0=Mon ... 4=Fri
start = Int("start")   # minutes since midnight (within work hours)
end = Int("end")

opt = Optimize()

# Domain constraints
opt.add(day >= 0, day <= 4)
opt.add(start >= work_start, end == start + duration, end <= work_end)

# Optional: align to 30-minute grid
opt.add(start % 30 == 0)

# No overlap helper: meeting [start, end) must not intersect any busy [s, e)
def add_no_overlap_for(person_busy):
    for d in range(5):
        for (s, e) in person_busy[d]:
            # If day == d then enforce non-overlap
            opt.add(Or(day != d, end <= s, start >= e))

# Add constraints for each participant
add_no_overlap_for(Brian_busy)
add_no_overlap_for(Julia_busy)

# Preferences:
# 1) Earliest availability across the week (minimize absolute minute-of-week)
total_minute_of_week = day * 24 * 60 + start
h1 = opt.minimize(total_minute_of_week)

# 2) Prefer to avoid Monday as a tiebreaker (if multiple earliest options)
monday_flag = If(day == 0, 1, 0)
h2 = opt.minimize(monday_flag)

if opt.check() == sat:
    model = opt.model()
    d_val = model.evaluate(day).as_long()
    s_val = model.evaluate(start).as_long()
    e_val = s_val + duration
    day_name = days[d_val]
    start_str = min_to_str(s_val)
    end_str = min_to_str(e_val)
    print(f"{day_name} {{{start_str}:{end_str}}}")
else:
    print("No feasible meeting time found.")