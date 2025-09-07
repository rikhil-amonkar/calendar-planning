from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()
start = Int('start')

# Work hours from 9:00 (540 min) to 17:00 (1020 min)
# Meeting must end by 15:30 (930 min) due to Jose's constraint
solver.add(start >= 540)
solver.add(start + 30 <= 930)

# Jose's busy intervals (11:00-11:30, 12:30-13:00)
jose_busy = [(660, 690), (750, 780)]
for b_start, b_end in jose_busy:
    solver.add(Or(start >= b_end, start + 30 <= b_start))

# Keith's busy intervals (14:00-14:30, 15:00-15:30)
keith_busy = [(840, 870), (900, 930)]
for b_start, b_end in keith_busy:
    solver.add(Or(start >= b_end, start + 30 <= b_start))

# Logan's busy intervals (9:00-10:00, 12:00-12:30, 15:00-15:30)
logan_busy = [(540, 600), (720, 750), (900, 930)]
for b_start, b_end in logan_busy:
    solver.add(Or(start >= b_end, start + 30 <= b_start))

# Megan's busy intervals (9:00-10:30, 11:00-12:00, 13:00-13:30, 14:30-16:30)
megan_busy = [(540, 630), (660, 720), (780, 810), (870, 990)]
for b_start, b_end in megan_busy:
    solver.add(Or(start >= b_end, start + 30 <= b_start))

# Gary's busy intervals (9:00-9:30, 10:00-10:30, 11:30-13:00, 13:30-14:00, 14:30-16:30)
gary_busy = [(540, 570), (600, 630), (690, 780), (810, 840), (870, 990)]
for b_start, b_end in gary_busy:
    solver.add(Or(start >= b_end, start + 30 <= b_start))

# Bobby's busy intervals (11:00-11:30, 12:00-12:30, 13:00-16:00)
bobby_busy = [(660, 690), (720, 750), (780, 960)]
for b_start, b_end in bobby_busy:
    solver.add(Or(start >= b_end, start + 30 <= b_start))

if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    day = "Monday"
    start_time = minutes_to_time(start_val)
    end_time = minutes_to_time(start_val + 30)
    print(f"{start_time}:{end_time} {day}")
else:
    print("No solution found")