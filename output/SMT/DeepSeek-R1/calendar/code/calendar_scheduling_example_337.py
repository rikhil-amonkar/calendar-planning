from z3 import *

# Define participants' busy times in minutes since 9:00 for Monday
john = [(150, 180), (300, 330)]  # 11:30-12:00, 14:00-14:30
megan = [(180, 210), (300, 360), (390, 420)]  # 12:00-12:30, 14:00-15:00, 15:30-16:00
kimberly = [(0, 30), (60, 90), (120, 330), (360, 420), (450, 480)]  # 9:00-9:30, 10:00-10:30, 11:00-14:30, 15:00-16:00, 16:30-17:00
sean = [(60, 120), (150, 300), (360, 390)]  # 10:00-11:00, 11:30-14:00, 15:00-15:30
lori = [(0, 30), (90, 180), (240, 330), (420, 450)]  # 9:00-9:30, 10:30-12:00, 13:00-14:30, 16:00-16:30

# Create variable and optimizer
start_time = Int('start_time')
opt = Optimize()

# Meeting must be 30 minutes within 9:00-17:00 (480 minutes)
opt.add(start_time >= 0, start_time + 30 <= 480)

# Function to add availability constraints
def add_availability(busy_slots):
    for (s, e) in busy_slots:
        opt.add(Or(start_time >= e, start_time + 30 <= s))

# Add constraints for all participants except Brandon (no meetings)
add_availability(john)
add_availability(megan)
add_availability(kimberly)
add_availability(sean)
add_availability(lori)

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