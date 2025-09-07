from z3 import *

# Days: 0=Monday, 1=Tuesday, 2=Wednesday
days = ["Monday", "Tuesday", "Wednesday"]

# Time is measured in minutes from 09:00 (0) to 17:00 (480)
MEETING_DURATION = 30

# Busy schedules per person per day as intervals [start, end) in minutes from 09:00
# Nicole
nicole_busy = {
    0: [(0, 30), (240, 270), (330, 390)],          # Monday: 9:00-9:30, 13:00-13:30, 14:30-15:30
    1: [(0, 30), (150, 270), (330, 390)],          # Tuesday: 9:00-9:30, 11:30-13:30, 14:30-15:30
    2: [(60, 120), (210, 360), (420, 480)],        # Wednesday: 10:00-11:00, 12:30-15:00, 16:00-17:00
}

# Ruth
ruth_busy = {
    0: [(0, 480)],                                  # Monday: 9:00-17:00
    1: [(0, 480)],                                  # Tuesday: 9:00-17:00
    2: [(0, 90), (120, 150), (180, 210), (270, 390), (420, 450)],  # Wednesday
}

def no_overlap_constraints(S, E, intervals):
    # For all busy intervals [b_start, b_end), require meeting [S,E) does not intersect
    # Non-overlap condition: E <= b_start or S >= b_end
    return And([Or(E <= b_start, S >= b_end) for (b_start, b_end) in intervals]) if intervals else True

# Variables
D = Int('D')         # day index: 0..2
S = Int('S')         # start time in minutes from 09:00 (0..450, step 30)
E = S + MEETING_DURATION

s = Solver()

# Domain constraints
s.add(D >= 0, D <= 2)
s.add(S >= 0, E <= 480)
s.add(S % 30 == 0)

# Availability constraints per day
for d in [0, 1, 2]:
    s.add(Implies(D == d, no_overlap_constraints(S, E, nicole_busy[d])))
    s.add(Implies(D == d, no_overlap_constraints(S, E, ruth_busy[d])))

# Preference/constraint: Ruth does not want to meet on Wednesday after 13:30
# Enforce that if day is Wednesday (2), meeting ends no later than 13:30 (which is 270 minutes from 09:00)
s.add(Implies(D == 2, E <= 270))

# Solve
if s.check() == z3.sat:
    m = s.model()
    d_val = m[D].as_long()
    s_val = m[S].as_long()
    e_val = s_val + MEETING_DURATION

    # Convert to absolute clock time (from midnight) for pretty-printing
    start_abs = 9*60 + s_val
    end_abs = 9*60 + e_val

    def fmt(mm):
        h = mm // 60
        m_ = mm % 60
        return f"{h:02d}:{m_:02d}"

    day_name = days[d_val]
    start_str = fmt(start_abs)
    end_str = fmt(end_abs)

    print(day_name)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No feasible time found.")