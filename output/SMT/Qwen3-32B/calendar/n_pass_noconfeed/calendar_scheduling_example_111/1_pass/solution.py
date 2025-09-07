from z3 import *

def minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Create solver
s = Solver()

# Variable for start time (in minutes since midnight)
start = Int('start')
# Meeting is between 9:00 (540) and 17:00 (1020), duration 30 mins => start <= 990
s.add(And(start >= 540, start <= 990))

# Gregory's blocked intervals (in minutes)
greg_blocked = [
    (540, 600),   # 9:00-10:00
    (630, 690),   # 10:30-11:30
    (750, 780),   # 12:30-13:00
    (810, 840)    # 13:30-14:00
]
for b_start, b_end in greg_blocked:
    s.add(Or(start + 30 <= b_start, start >= b_end))

# Christine's blocked intervals
christine_blocked = [
    (540, 690),   # 9:00-11:30
    (810, 1020)   # 13:30-17:00
]
for b_start, b_end in christine_blocked:
    s.add(Or(start + 30 <= b_start, start >= b_end))

# Vincent's blocked intervals
vincent_blocked = [
    (540, 570),   # 9:00-9:30
    (630, 720),   # 10:30-12:00
    (750, 840),   # 12:30-14:00
    (870, 1020)   # 14:30-17:00
]
for b_start, b_end in vincent_blocked:
    s.add(Or(start + 30 <= b_start, start >= b_end))

if s.check() == sat:
    m = s.model()
    start_val = m[start].as_long()
    # Convert start time to HH:MM
    start_h = start_val // 60
    start_m = start_val % 60
    end_val = start_val + 30
    end_h = end_val // 60
    end_m = end_val % 60
    print(f"Monday {start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}")
else:
    print("No solution")