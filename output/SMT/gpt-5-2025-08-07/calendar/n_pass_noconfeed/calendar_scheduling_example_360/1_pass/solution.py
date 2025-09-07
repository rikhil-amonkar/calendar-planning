from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Create solver
s = Solver()

# Variables
start = Int('start')
end = Int('end')
duration = 30  # minutes

# Work hours: 09:00 to 17:00 on Monday
work_start = minutes(9, 0)
work_end = minutes(17, 0)

# Meeting duration and within work hours
s.add(end == start + duration)
s.add(start >= work_start, end <= work_end)

# Helper to assert no-overlap between [start, end) and a busy interval [bstart, bend)
def avoid_busy(bstart, bend):
    return Or(end <= bstart, start >= bend)

# Emily: 10:00-10:30, 16:00-16:30
s.add(avoid_busy(minutes(10,0), minutes(10,30)))
s.add(avoid_busy(minutes(16,0), minutes(16,30)))

# Mason: free all day (no constraints)

# Maria: 10:30-11:00, 14:00-14:30
s.add(avoid_busy(minutes(10,30), minutes(11,0)))
s.add(avoid_busy(minutes(14,0), minutes(14,30)))

# Carl: 9:30-10:00, 10:30-12:30, 13:30-14:00, 14:30-15:30, 16:00-17:00
s.add(avoid_busy(minutes(9,30), minutes(10,0)))
s.add(avoid_busy(minutes(10,30), minutes(12,30)))
s.add(avoid_busy(minutes(13,30), minutes(14,0)))
s.add(avoid_busy(minutes(14,30), minutes(15,30)))
s.add(avoid_busy(minutes(16,0), minutes(17,0)))

# David: 9:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-15:00, 16:00-17:00
s.add(avoid_busy(minutes(9,30), minutes(11,0)))
s.add(avoid_busy(minutes(11,30), minutes(12,0)))
s.add(avoid_busy(minutes(12,30), minutes(13,30)))
s.add(avoid_busy(minutes(14,0), minutes(15,0)))
s.add(avoid_busy(minutes(16,0), minutes(17,0)))

# Frank: 9:30-10:30, 11:00-11:30, 12:30-13:30, 14:30-17:00
s.add(avoid_busy(minutes(9,30), minutes(10,30)))
s.add(avoid_busy(minutes(11,0), minutes(11,30)))
s.add(avoid_busy(minutes(12,30), minutes(13,30)))
s.add(avoid_busy(minutes(14,30), minutes(17,0)))

if s.check() == sat:
    m = s.model()
    st = m[start].as_long()
    en = m[end].as_long()
    print(f"Monday {{{fmt(st)}:{fmt(en)}}}")
else:
    print("No feasible time found.")