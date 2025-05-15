from z3 import Solver, Int, Or, Optimize, sat

solver = Optimize()
Start = Int('Start')

# Convert time to minutes since 9:00 across all days (Monday=0-480, Tuesday=480-960, Wednesday=960-1440, Thursday=1440-1920)
solver.add(Start >= 480)  # Monday excluded (Betty can't meet)
solver.add(Start + 30 <= 1920)  # Latest end: Thursday 17:00

# Function to add blocked time ranges
def add_blocks(blocks):
    for block_start, block_end in blocks:
        solver.add(Or(Start + 30 <= block_start, Start >= block_end))

# Betty's constraints
# Tuesday (480-960): available after 840 (15:00), blocks: 480-510,630-660,690-720,750-780,930-960
solver.add(Or(Start < 480, Start >= 840))  # Tuesday availability
add_blocks([(480,510),(630,660),(690,720),(750,780),(930,960)])

# Wednesday (960-1440): blocks 990-1050,1200-1230,1260-1290
add_blocks([(990,1050),(1200,1230),(1260,1290)])

# Thursday (1440-1920): available after 1800 (15:00), blocks:1470-1500,1590-1620,1740-1770,1800-1830,1890-1920
solver.add(Or(Start < 1440, Start >= 1800))  # Thursday availability
add_blocks([(1470,1500),(1590,1620),(1740,1770),(1800,1830),(1890,1920)])

# Scott's constraints
# Tuesday (480-960): blocks 480-510,540-600,630-660,690-720,780-840,900-930
add_blocks([(480,510),(540,600),(630,660),(690,720),(780,840),(900,930)])

# Wednesday (960-1440): blocks 990-1170,1200-1230,1260-1290,1320-1350,1380-1410
add_blocks([(990,1170),(1200,1230),(1260,1290),(1320,1350),(1380,1410)])

# Thursday (1440-1920): blocks1440-1470,1500-1530,1560-1620,1650-1680,1800-1860,1890-1920
add_blocks([(1440,1470),(1500,1530),(1560,1620),(1650,1680),(1800,1860),(1890,1920)])

# Find earliest possible time
solver.minimize(Start)

if solver.check() == sat:
    model = solver.model()
    start_global = model[Start].as_long()
    
    # Determine day and local time
    if start_global < 960:
        day = "Tuesday"
        start_local = start_global - 480
    elif start_global < 1440:
        day = "Wednesday"
        start_local = start_global - 960
    else:
        day = "Thursday"
        start_local = start_global - 1440
    
    start_h = 9 + start_local // 60
    start_m = start_local % 60
    end_local = start_local + 30
    end_h = 9 + end_local // 60
    end_m = end_local % 60
    
    print(f"{day} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")