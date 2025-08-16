import z3

# Initialize the optimizer
opt = z3.Optimize()

# Define the start time variable in minutes since midnight
start = z3.Int('start')

# Define the work day boundaries (9:00 AM to 5:00 PM)
opt.add(start >= 9 * 60)  # 9:00 AM
opt.add(start <= 17 * 60 - 30)  # 5:00 PM minus 30 minutes for the meeting duration

# Adam's busy times on Monday in minutes since midnight
adam_busies = [
    (9 * 60 + 30, 10 * 60),  # 9:30-10:00
    (12 * 60 + 30, 13 * 60), # 12:30-13:00
    (14 * 60 + 30, 15 * 60), # 14:30-15:00
    (16 * 60 + 30, 17 * 60)  # 16:30-17:00
]

# Roy's busy times on Monday in minutes since midnight
roy_busies = [
    (10 * 60, 11 * 60),        # 10:00-11:00
    (11 * 60 + 30, 13 * 60),   # 11:30-13:00
    (13 * 60 + 30, 14 * 60 + 30), # 13:30-14:30
    (16 * 60 + 30, 17 * 60)    # 16:30-17:00
]

# Add constraints for Adam's busy times
for b_start, b_end in adam_busies:
    opt.add(z3.Or(start + 30 <= b_start, start >= b_end))

# Add constraints for Roy's busy times
for b_start, b_end in roy_busies:
    opt.add(z3.Or(start + 30 <= b_start, start >= b_end))

# Minimize the start time to find the earliest possible slot
opt.minimize(start)

# Check for a solution and output the result
if opt.check() == z3.sat:
    model = opt.model()
    start_val = model[start].as_long()
    day = "Monday"
    start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
    end_time = f"{(start_val + 30) // 60:02d}:{(start_val + 30) % 60:02d}"
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")