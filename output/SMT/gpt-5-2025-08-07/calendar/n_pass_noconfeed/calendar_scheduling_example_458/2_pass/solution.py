from z3 import Optimize, Int, Or, sat

def m(h, mi):
    return h * 60 + mi

def to_hhmm(total_minutes):
    h = total_minutes // 60
    mi = total_minutes % 60
    return f"{h:02d}:{mi:02d}"

# Meeting parameters
day = "Monday"
work_start = m(9, 0)
work_end = m(17, 0)
duration = 30  # minutes

# Participants' busy schedules on Monday (in minutes from 00:00)
busy = {
    "Wayne": [],
    "Melissa": [
        (m(10, 0), m(11, 0)),
        (m(12, 30), m(14, 0)),
        (m(15, 0), m(15, 30)),
    ],
    "Catherine": [],
    "Gregory": [
        (m(12, 30), m(13, 0)),
        (m(15, 30), m(16, 0)),
    ],
    "Victoria": [
        (m(9, 0), m(9, 30)),
        (m(10, 30), m(11, 30)),
        (m(13, 0), m(14, 0)),
        (m(14, 30), m(15, 0)),
        (m(15, 30), m(16, 30)),
    ],
    "Thomas": [
        (m(10, 0), m(12, 0)),
        (m(12, 30), m(13, 0)),
        (m(14, 30), m(16, 0)),
    ],
    "Jennifer": [
        (m(9, 0), m(9, 30)),
        (m(10, 0), m(10, 30)),
        (m(11, 0), m(13, 0)),
        (m(13, 30), m(14, 30)),
        (m(15, 0), m(15, 30)),
        (m(16, 0), m(16, 30)),
    ],
}

# Z3 optimization model
opt = Optimize()
start = Int("start")
end = Int("end")

# Basic bounds and duration
opt.add(start >= work_start)
opt.add(end == start + duration)
opt.add(end <= work_end)

# No-overlap constraints for each participant's busy intervals
for person, intervals in busy.items():
    for (s, e) in intervals:
        opt.add(Or(end <= s, start >= e))

# Preference: Wayne would like to avoid meetings before 14:00
opt.add_soft(start >= m(14, 0), weight="1")

# Among preferred times, choose the earliest feasible start
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s_val = model.eval(start).as_long()
    e_val = s_val + duration
    print(day)
    print("{" + f"{to_hhmm(s_val)}:{to_hhmm(e_val)}" + "}")
else:
    print("No solution found")