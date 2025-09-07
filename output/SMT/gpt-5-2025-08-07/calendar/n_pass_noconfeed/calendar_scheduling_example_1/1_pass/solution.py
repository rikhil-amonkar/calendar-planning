from z3 import Optimize, Int, Or

def tm(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Problem data
day = "Monday"
work_start = tm("09:00")
work_end   = tm("17:00")
duration = 30  # minutes

# Existing schedules (busy intervals) for Monday
raymond_busy = [
    (tm("09:00"), tm("09:30")),
    (tm("11:30"), tm("12:00")),
    (tm("13:00"), tm("13:30")),
    (tm("15:00"), tm("15:30")),
]

billy_busy = [
    (tm("10:00"), tm("10:30")),
    (tm("12:00"), tm("13:00")),
    (tm("16:30"), tm("17:00")),
]

donald_busy = [
    (tm("09:00"), tm("09:30")),
    (tm("10:00"), tm("11:00")),
    (tm("12:00"), tm("13:00")),
    (tm("14:00"), tm("14:30")),
    (tm("16:00"), tm("17:00")),
]

# SMT model
opt = Optimize()
start = Int("start")

# Working hours and half-hour alignment
opt.add(start >= work_start)
opt.add(start + duration <= work_end)
opt.add(start % 30 == 0)  # align to 30-minute grid

# No-overlap constraints
def no_overlap(busy_list):
    for (b_start, b_end) in busy_list:
        opt.add(Or(start + duration <= b_start, start >= b_end))

no_overlap(raymond_busy)
no_overlap(billy_busy)
no_overlap(donald_busy)

# Preference: Billy would like to avoid meetings after 15:00
opt.add_soft(start + duration <= tm("15:00"), "1")

# Secondary objective: earliest possible time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s = model[start].as_long()
    e = s + duration
    print(f"{day} {{{fmt(s)}:{fmt(e)}}}")
else:
    print("No feasible meeting time found.")