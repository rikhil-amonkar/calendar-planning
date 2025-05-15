from z3 import Solver, Int, Or, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Basic constraints: 30-minute meeting between 9:00 (0 min) and 17:00 (480 min)
solver.add(Start >= 0)
solver.add(Start + 30 <= 480)

# Function to add blocked time constraints
def add_blocks(blocks):
    for block_start, block_end in blocks:
        solver.add(Or(Start + 30 <= block_start, Start >= block_end))

# Gregory's blocked times (9:00-9:30, 11:30-12:00)
add_blocks([(0, 30), (150, 180)])

# Jonathan's meetings (9:00-9:30, 12:00-12:30, 13:00-13:30, 15:00-16:00, 16:30-17:00)
add_blocks([(0, 30), (180, 210), (240, 270), (360, 420), (450, 480)])

# Barbara's meetings (10:00-10:30, 13:30-14:00)
add_blocks([(60, 90), (270, 300)])

# Jesse's busy times (10:00-11:00, 12:30-14:30)
add_blocks([(60, 120), (210, 330)])

# Alan's busy times (9:30-11:00, 11:30-12:30, 13:00-15:30, 16:00-17:00)
add_blocks([(30, 120), (150, 210), (240, 390), (420, 480)])

# Nicole's blocked times (9:00-10:30, 11:30-12:00, 12:30-13:30, 14:00-17:00)
add_blocks([(0, 90), (150, 180), (210, 270), (300, 480)])

# Catherine's busy times (9:00-10:30, 12:00-13:30, 15:00-15:30, 16:00-16:30)
add_blocks([(0, 90), (180, 270), (360, 390), (420, 450)])

# Find earliest possible time
solver.minimize(Start)

if solver.check() == sat:
    model = solver.model()
    start_min = model[Start].as_long()
    start_h = 9 + start_min // 60
    start_m = start_min % 60
    end_min = start_min + 30
    end_h = 9 + end_min // 60
    end_m = end_min % 60
    print(f"Monday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")