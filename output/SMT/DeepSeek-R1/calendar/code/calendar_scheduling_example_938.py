from z3 import *

s = Optimize()
day = Int('day')
start = Int('start')

s.add(day >= 0, day <= 4)  # 0:Monday - 4:Friday
s.add(start >= 0, start + 30 <= 480)  # 30min meeting within 9:00-17:00

# Create day-specific constraints using implications
def add_day_constraints(day_num, eugene_busy, eric_busy):
    constraints = []
    # Add Eugene's busy slots
    for (b_start, b_end) in eugene_busy:
        constraints.append(Or(start + 30 <= b_start, start >= b_end))
    # Add Eric's busy slots
    for (b_start, b_end) in eric_busy:
        constraints.append(Or(start + 30 <= b_start, start >= b_end))
    s.add(Implies(day == day_num, And(constraints)))

# Monday - Both busy all day (no solution)
add_day_constraints(0, 
    [(120,180),(270,300),(330,360),(420,450)],  # Eugene
    [(0,480)]  # Eric (all day)
)

# Tuesday - Eric busy all day
add_day_constraints(1,
    [],  # Eugene free
    [(0,480)]  # Eric
)

# Wednesday 
add_day_constraints(2,
    [(0,30),(120,150),(180,210),(270,360)],  # Eugene
    [(0,150),(180,300),(330,450)]  # Eric
)

# Thursday - Eric busy all day
add_day_constraints(3,
    [(30,60),(120,210)],  # Eugene
    [(0,480)]  # Eric
)

# Friday 
add_day_constraints(4,
    [(90,120),(180,210),(240,270)],  # Eugene
    [(0,120),(210,480)]  # Eric
)

# Optimize: Avoid Wednesday (day 2) first, then earliest time
penalty = If(day == 2, 100000, 0)  # Heavy penalty for Wednesday
s.minimize(penalty + day*1000 + start)  # Prioritize non-Wednesdays

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ["Monday","Tuesday","Wednesday","Thursday","Friday"]
    hours = 9 + st//60
    minutes = st%60
    print(f"Meeting can be scheduled on {days[d]} at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found.")