from z3 import Solver, Int, Or, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Convert time to minutes since 9:00 (e.g., 9:30 = 30, 10:00 = 60)
solver.add(Start >= 0)               # Earliest possible start: 9:00
solver.add(Start + 30 <= 480)        # Latest possible end: 17:00

# Function to add blocked time constraints
def add_blocks(blocks):
    for block_start, block_end in blocks:
        solver.add(Or(Start + 30 <= block_start, Start >= block_end))

# Lisa's blocked times: 9:00-9:30, 10:30-11:00, 14:00-16:00
add_blocks([(0, 30), (90, 120), (300, 420)])

# Anthony's blocked times: 9:00-9:30, 11:00-11:30, 12:30-13:30, 14:00-15:00, 15:30-16:00, 16:30-17:00
add_blocks([(0, 30), (120, 150), (210, 270), (300, 360), (390, 420), (450, 480)])

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