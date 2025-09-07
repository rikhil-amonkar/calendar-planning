from z3 import *

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 0         # 9:00 -> offset 0
WORK_END = 8 * 60      # 17:00 -> offset 480

# Day encoding: 0 = Monday, 1 = Tuesday
MONDAY, TUESDAY = 0, 1

# Busy intervals as (start_minute_from_9, end_minute_from_9)
amanda_busy = {
    MONDAY:  [(0, 90), (120, 150), (210, 240), (270, 300), (330, 360)],
    TUESDAY: [(0, 30), (60, 90), (150, 180), (270, 330), (390, 420), (450, 480)],
}
nathan_busy = {
    MONDAY:  [(60, 90), (120, 150), (270, 330), (420, 450)],
    TUESDAY: [(0, 90), (120, 240), (270, 300), (330, 390), (420, 450)],
}

# Helper to assert no overlap with busy intervals
def no_overlap(start, end, intervals):
    return And(*[Or(end <= s, start >= e) for (s, e) in intervals]) if intervals else True

# Z3 variables
day = Int('day')
start = Int('start')
end = Int('end')

s = Solver()

# Basic constraints
s.add(Or(day == MONDAY, day == TUESDAY))
s.add(end == start + DURATION)
s.add(start >= WORK_START, end <= WORK_END)

# Work-hours 9:00-17:00 implies start in [0, WORK_END - DURATION]
s.add(start <= WORK_END - DURATION)

# Availability constraints by day
s.add(If(day == MONDAY,
         And(no_overlap(start, end, amanda_busy[MONDAY]),
             no_overlap(start, end, nathan_busy[MONDAY])),
         True))
s.add(If(day == TUESDAY,
         And(no_overlap(start, end, amanda_busy[TUESDAY]),
             no_overlap(start, end, nathan_busy[TUESDAY])),
         True))

# Additional constraints:
# - Amanda does not want to meet on Tuesday after 11:00 -> meeting must end by 11:00 on Tuesday
s.add(If(day == TUESDAY, end <= 120, True))

# - Nathan cannot meet on Monday
s.add(day == TUESDAY)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    en = m[end].as_long()

    def mm_to_hhmm(offset_minutes):
        total_minutes = 9 * 60 + offset_minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    day_name = ["Monday", "Tuesday"][d]
    start_str = mm_to_hhmm(st)
    end_str = mm_to_hhmm(en)
    # Output includes both the day and the time range like {HH:MM:HH:MM}
    print(f"{day_name} {{{start_str}:{end_str}}}")
else:
    print("No solution found.")