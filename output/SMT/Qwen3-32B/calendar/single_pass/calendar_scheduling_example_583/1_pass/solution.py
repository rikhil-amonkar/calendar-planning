import z3

opt = z3.Optimize()

start_time = z3.Int('start_time')

# Define the work hours constraints (9:00 to 17:00, 30 minutes before 17:00)
opt.add(start_time >= 9 * 60)
opt.add(start_time <= 17 * 60 - 30)

# Busy intervals for Lisa and Anthony in minutes since midnight
lisa_busy = [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60), (14 * 60, 16 * 60)]
anthony_busy = [(9 * 60, 9 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60 + 30),
                (14 * 60, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]

# Combine busy intervals
all_busy = lisa_busy + anthony_busy

# Add constraints to avoid overlapping with busy intervals
for start_b, end_b in all_busy:
    opt.add(z3.Or(start_time >= end_b, start_b >= start_time + 30))

# Minimize the start time to find the earliest possible slot
opt.minimize(start_time)

if opt.check() == z3.sat:
    model = opt.model()
    start = model[start_time].as_long()
    end = start + 30
    day = "Monday"
    
    # Helper function to convert minutes to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {format_time(start)}")
    print(f"End Time: {format_time(end)}")
else:
    print("No solution found.")