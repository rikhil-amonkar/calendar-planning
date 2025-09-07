from z3 import *

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60
WORK_END = 17 * 60
DAY_START_OFFSET = WORK_START  # minutes from 00:00
WORK_WINDOW = WORK_END - WORK_START

# Days: 0 = Monday, 1 = Tuesday
day = Int('day')
start = Int('start')  # minutes from 9:00 within the chosen day

s = Solver()

# Working hours constraint within the day window
s.add(Or(day == 0, day == 1))
s.add(start >= 0)
s.add(start + DURATION <= WORK_WINDOW)

# Existing schedules (times converted to minutes from 9:00)
def m(h, m):  # minutes from 9:00 within the day
    return (h * 60 + m) - DAY_START_OFFSET

# Busy intervals per person per day as (start, end) half-open [start, end)
margaret_busy = {
    0: [ (m(10,30), m(11,00)),
         (m(11,30), m(12,00)),
         (m(13,00), m(13,30)),
         (m(15,00), m(17,00)) ],
    1: [ (m(12,00), m(12,30)) ]
}

alexis_busy = {
    0: [ (m(9,30),  m(11,30)),
         (m(12,30), m(13,00)),
         (m(14,00), m(17,00)) ],
    1: [ (m(9,00),  m(9,30)),
         (m(10,00), m(10,30)),
         (m(14,00), m(16,30)) ]
}

def no_overlap_constraints(day_var, start_var, duration, busy_by_day):
    cs = []
    for d in [0, 1]:
        for (bs, be) in busy_by_day[d]:
            cs.append(Implies(day_var == d, Or(start_var + duration <= bs, start_var >= be)))
    return cs

# Add non-overlap constraints for each participant
s.add(no_overlap_constraints(day, start, DURATION, margaret_busy))
s.add(no_overlap_constraints(day, start, DURATION, alexis_busy))

# Preferences:
# - Margaret does not want to meet on Monday
# - Margaret does not want to meet on Tuesday before 14:30
# Therefore: day == Tuesday and start >= 14:30 - 9:00 = 330 minutes from 9:00
s.add(day == 1)
s.add(start >= ((14 * 60 + 30) - DAY_START_OFFSET))  # 14:30 from 9:00 => 330

if s.check() == sat:
    model = s.model()
    d_val = model[day].as_long()
    st = model[start].as_long()
    et = st + DURATION

    def fmt_time(offset_from_9):
        abs_minutes = DAY_START_OFFSET + offset_from_9
        hh = abs_minutes // 60
        mm = abs_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    day_name = ["Monday", "Tuesday"][d_val]
    start_str = fmt_time(st)
    end_str = fmt_time(et)

    # Output: day on one line, time range in braces on the next line
    print(day_name)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No solution found.")