from z3 import Solver, Int, Or, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Convert time to minutes (Monday=0-480, Tuesday=480-960)
solver.add(Start >= 480)          # Monday excluded (Jesse is fully busy)
solver.add(Start + 60 <= 960)     # Meeting must end by Tuesday 17:00

# Function to add blocked time constraints
def add_blocks(blocks):
    for block_start, block_end in blocks:
        solver.add(Or(Start + 60 <= block_start, Start >= block_end))

# Patricia's Tuesday blocked times (global minutes)
add_blocks([(540,570), (600,660), (780,900), (930,960)])

# Jesse's Tuesday blocked times (global minutes)
add_blocks([(600,630), (660,690), (720,780), (810,840), (870,960)])

# Find earliest possible time
solver.minimize(Start)

if solver.check() == sat:
    model = solver.model()
    start_global = model[Start].as_long()
    start_local = start_global - 480  # Convert to Tuesday minutes
    start_h = 9 + start_local // 60
    start_m = start_local % 60
    end_h = 9 + (start_local + 60) // 60
    end_m = (start_local + 60) % 60
    print(f"Tuesday {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")