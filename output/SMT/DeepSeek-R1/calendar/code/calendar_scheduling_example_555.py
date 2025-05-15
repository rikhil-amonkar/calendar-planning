from z3 import *

# Convert busy times to minutes since 9:00
randy = [(0, 90), (120, 390), (420, 480)]  # 9:00-10:30, 11:00-15:30, 16:00-17:00

# Create variable and optimizer
start_time = Int('start_time')
opt = Optimize()

# Meeting constraints: 30 minutes within 9:00-17:00 (480 minutes)
opt.add(start_time >= 0)
opt.add(start_time + 30 <= 480)

# Evelyn's constraint: Can't meet after 13:00 (240 minutes since 9:00)
opt.add(start_time + 30 <= 240)

# Function to add availability constraints
def add_availability(busy_slots):
    for (s, e) in busy_slots:
        opt.add(Or(start_time >= e, start_time + 30 <= s))

# Add constraints for Randy (Evelyn has no meetings)
add_availability(randy)

# Find earliest possible time
opt.minimize(start_time)

if opt.check() == sat:
    m = opt.model()
    s = m[start_time].as_long()
    start_h = 9 + s // 60
    start_m = s % 60
    end_time = s + 30
    end_h = 9 + end_time // 60
    end_m = end_time % 60
    print(f"Day: Monday, Start: {start_h:02}:{start_m:02}, End: {end_h:02}:{end_m:02}")
else:
    print("No solution found")