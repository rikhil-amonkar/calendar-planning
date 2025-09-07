import z3

# Time helpers
def to_min(h, m): 
    return h * 60 + m

def to_hhmm(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours
WORK_START = to_min(9, 0)   # 09:00
WORK_END   = to_min(17, 0)  # 17:00
MEETING_DURATION = 60       # 1 hour

# Days: 0 = Monday, 1 = Tuesday
day_names = {0: "Monday", 1: "Tuesday"}

# Busy intervals as half-open [start, end)
# Minutes from 00:00
busy = {
    0: {  # Monday
        "Gary": [
            (to_min(9,30),  to_min(10,0)),
            (to_min(11,0),  to_min(13,0)),
            (to_min(14,0),  to_min(14,30)),
            (to_min(16,30), to_min(17,0)),
        ],
        "David": [
            (to_min(9,0),   to_min(9,30)),
            (to_min(10,0),  to_min(13,0)),
            (to_min(14,30), to_min(16,30)),
        ],
    },
    1: {  # Tuesday
        "Gary": [
            (to_min(9,0),   to_min(9,30)),
            (to_min(10,30), to_min(11,0)),
            (to_min(14,30), to_min(16,0)),
        ],
        "David": [
            (to_min(9,0),   to_min(9,30)),
            (to_min(10,0),  to_min(10,30)),
            (to_min(11,0),  to_min(12,30)),
            (to_min(13,0),  to_min(14,30)),
            (to_min(15,0),  to_min(16,0)),
            (to_min(16,30), to_min(17,0)),
        ],
    },
}

# Z3 variables
day = z3.Int('day')      # 0 = Monday, 1 = Tuesday
start = z3.Int('start')  # meeting start in minutes since midnight
end = z3.Int('end')      # meeting end in minutes since midnight

def add_common_constraints(slv):
    slv.add(end == start + MEETING_DURATION)
    slv.add(z3.And(start >= WORK_START, end <= WORK_END))

def add_day_constraints(slv, d):
    # Meeting must not overlap busy intervals for this day
    for person in ["Gary", "David"]:
        for (b_start, b_end) in busy[d][person]:
            slv.add(z3.Or(end <= b_start, start >= b_end))

def find_earliest_slot():
    # Try earliest day first, then earliest 30-min slot
    for d in [0, 1]:
        solver = z3.Solver()
        add_common_constraints(solver)
        add_day_constraints(solver, d)
        solver.add(day == d)

        # Iterate over 30-minute aligned starts
        for s in range(WORK_START, WORK_END - MEETING_DURATION + 1, 30):
            solver.push()
            solver.add(start == s)
            if solver.check() == z3.sat:
                model = solver.model()
                return d, model[start].as_long(), model[end].as_long()
            solver.pop()
    return None

res = find_earliest_slot()
if res is None:
    print("No feasible meeting time found.")
else:
    d_val, s_val, e_val = res
    day_str = day_names[d_val]
    s_str = to_hhmm(s_val)
    e_str = to_hhmm(e_val)
    print(f"{day_str} {{{s_str}:{e_str}}}")