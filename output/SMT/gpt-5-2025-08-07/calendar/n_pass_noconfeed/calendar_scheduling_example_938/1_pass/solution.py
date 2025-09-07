from z3 import *

# Time helpers
def tm(hhmm):
    h, m = map(int, hhmm.split(':'))
    return h * 60 + m

def mm_to_hhmm(m):
    h = m // 60
    s = m % 60
    return f"{h:02d}:{s:02d}"

# Constants
MON, TUE, WED, THU, FRI = 0, 1, 2, 3, 4
DAY_NAMES = {MON: "Monday", TUE: "Tuesday", WED: "Wednesday", THU: "Thursday", FRI: "Friday"}

WORK_START = tm("09:00")
WORK_END   = tm("17:00")
DUR = 30  # minutes

# Busy schedules (inclusive start, exclusive end)
eugene_busy = {
    MON: [(tm("11:00"), tm("12:00")),
          (tm("13:30"), tm("14:00")),
          (tm("14:30"), tm("15:00")),
          (tm("16:00"), tm("16:30"))],
    TUE: [],
    WED: [(tm("09:00"), tm("09:30")),
          (tm("11:00"), tm("11:30")),
          (tm("12:00"), tm("12:30")),
          (tm("13:30"), tm("15:00"))],
    THU: [(tm("09:30"), tm("10:00")),
          (tm("11:00"), tm("12:30"))],
    FRI: [(tm("10:30"), tm("11:00")),
          (tm("12:00"), tm("12:30")),
          (tm("13:00"), tm("13:30"))],
}

eric_busy = {
    MON: [(tm("09:00"), tm("17:00"))],
    TUE: [(tm("09:00"), tm("17:00"))],
    WED: [(tm("09:00"), tm("11:30")),
          (tm("12:00"), tm("14:00")),
          (tm("14:30"), tm("16:30"))],
    THU: [(tm("09:00"), tm("17:00"))],
    FRI: [(tm("09:00"), tm("11:00")),
          (tm("11:30"), tm("17:00"))],
}

# Solver
opt = Optimize()

day   = Int('day')     # 0..4 -> Monday..Friday
start = Int('start')   # minutes since midnight
end   = Int('end')

# Basic bounds and duration
opt.add(day >= MON, day <= FRI)
opt.add(start >= WORK_START)
opt.add(end == start + DUR)
opt.add(end <= WORK_END)

# Align to 30-minute grid
opt.add(start % 30 == 0)

# Availability constraints per participant and day
def add_no_overlap_constraints(busy_map):
    for d in [MON, TUE, WED, THU, FRI]:
        for (s, e) in busy_map.get(d, []):
            # If meeting is on day d, it must not overlap (s, e)
            # No overlap: end <= s OR start >= e
            opt.add(Implies(day == d, Or(end <= s, start >= e)))

add_no_overlap_constraints(eugene_busy)
add_no_overlap_constraints(eric_busy)

# Preference: Eric would like to avoid more meetings on Wednesday
opt.add_soft(day != WED, weight='1')

# Solve
if opt.check() != sat:
    print("No feasible meeting time found.")
else:
    model = opt.model()
    d_val = model[day].as_long()
    s_val = model[start].as_long()
    e_val = model[end].as_long()

    day_str = DAY_NAMES[d_val]
    start_str = mm_to_hhmm(s_val)
    end_str = mm_to_hhmm(e_val)

    # Output includes day and time in {HH:MM:HH:MM}
    print(f"{day_str} {{{start_str}:{end_str}}}")