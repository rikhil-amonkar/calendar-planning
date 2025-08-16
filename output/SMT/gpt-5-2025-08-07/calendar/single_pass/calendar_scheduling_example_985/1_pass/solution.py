from z3 import Int, Solver, And, Or, Implies, sat

# Days mapping
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
MON, TUE, WED, THU, FRI = range(5)

# Meeting duration in minutes
duration = 60

# Busy schedules in minutes relative to 09:00 (i.e., 09:00 -> 0, 17:00 -> 480)
# Diane's schedule
diane_busy = {
    MON: [(180, 210), (360, 390)],                          # 12:00-12:30, 15:00-15:30
    TUE: [(60, 120), (150, 180), (210, 240), (420, 480)],   # 10:00-11:00, 11:30-12:00, 12:30-13:00, 16:00-17:00
    WED: [(0, 30), (330, 360), (450, 480)],                 # 09:00-09:30, 14:30-15:00, 16:30-17:00
    THU: [(390, 450)],                                      # 15:30-16:30
    FRI: [(30, 150), (330, 360), (420, 480)],               # 09:30-11:30, 14:30-15:00, 16:00-17:00
}

# Matthew's schedule
matthew_busy = {
    MON: [(0, 60), (90, 480)],                              # 09:00-10:00, 10:30-17:00
    TUE: [(0, 480)],                                        # 09:00-17:00
    WED: [(0, 120), (180, 330), (420, 480)],                # 09:00-11:00, 12:00-14:30, 16:00-17:00
    THU: [(0, 420)],                                        # 09:00-16:00
    FRI: [(0, 480)],                                        # 09:00-17:00
}

def no_overlap_constraints(day_var, start_var, busy):
    cons = []
    for d in range(5):
        for (bs, be) in busy.get(d, []):
            # Meeting [start, start+duration) should not overlap [bs, be)
            cons.append(Implies(day_var == d, Or(start_var + duration <= bs, start_var >= be)))
    return cons

def fmt_time(minutes_from_start):
    total = 9*60 + minutes_from_start
    hh = total // 60
    mm = total % 60
    return f"{hh:02d}:{mm:02d}"

# Z3 variables
day = Int('day')      # 0=Mon ... 4=Fri
start = Int('start')  # minutes from 09:00

s = Solver()

# Work hours: 09:00 to 17:00 -> 0 to 480, ensure meeting ends by 480
s.add(day >= 0, day <= 4)
s.add(start >= 0, start <= 480 - duration)

# Optional: choose starts on 30-minute boundaries for clean times
s.add(start % 30 == 0)

# No overlap constraints
s.add(no_overlap_constraints(day, start, diane_busy))
s.add(no_overlap_constraints(day, start, matthew_busy))

# Preference: Matthew would rather not meet on Wednesday before 12:30
# Enforce as a constraint: if Wednesday, start >= 12:30 -> 210 minutes from 09:00
s.add(Implies(day == WED, start >= 210))

if s.check() == sat:
    m = s.model()
    d_val = m[day].as_long()
    s_val = m[start].as_long()
    e_val = s_val + duration

    print("SOLUTION:")
    print(f"Day: {days[d_val]}")
    print(f"Start Time: {fmt_time(s_val)}")
    print(f"End Time: {fmt_time(e_val)}")
else:
    print("SOLUTION:")
    print("Day: None")
    print("Start Time: 00:00")
    print("End Time: 00:00")