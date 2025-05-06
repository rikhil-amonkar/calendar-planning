from z3 import Solver, Int, Or, And, sat

s = Solver()
day = Int('day')
start = Int('start')

# Days: 0=Mon,1=Tue,2=Wed,3=Thu,4=Fri
s.add(day == 1)  # Constraint: Only Tuesday allowed
s.add(start >= 180, start + 30 <= 480)  # Tuesday 12:00-16:30 (converted to minutes)

# Daniel's Tuesday busy intervals (minutes since 9:00)
daniel_busy = [(120, 180), (240, 270), (390, 420), (450, 480)]
for s_start, s_end in daniel_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Bradley's Tuesday busy intervals
bradley_busy = [(180, 240), (270, 300), (390, 450)]
for s_start, s_end in bradley_busy:
    s.add(Or(start + 30 <= s_start, start >= s_end))

# Find earliest time
s.minimize(start)

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_long()
    hours = start_time // 60 + 9
    minutes = start_time % 60
    print(f"Meeting starts on Tuesday at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")