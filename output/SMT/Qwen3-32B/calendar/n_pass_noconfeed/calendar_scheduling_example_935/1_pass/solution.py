from z3 import *

# Define busy intervals for Terry and Frances on each day (0=Monday, 1=Tuesday, ..., 4=Friday)
# Each interval is (start, end) in minutes since 9:00
terry_busy = {
    0: [(90, 120), (210, 300), (360, 480)],  # Monday
    1: [(30, 60), (90, 120), (300, 330), (420, 450)],  # Tuesday
    2: [(30, 90), (120, 180), (210, 240), (360, 420), (450, 480)],  # Wednesday
    3: [(30, 60), (180, 210), (240, 330), (420, 450)],  # Thursday
    4: [(0, 150), (180, 210), (270, 420), (450, 480)],  # Friday
}

frances_busy = {
    0: [(30, 120), (150, 240), (300, 330), (360, 420)],  # Monday
    1: [(0, 30), (60, 90), (120, 180), (240, 330), (390, 450)],  # Tuesday
    2: [(30, 60), (90, 120), (150, 420), (450, 480)],  # Wednesday
    3: [(120, 210), (330, 480)],  # Thursday
    4: [(30, 90), (120, 210), (270, 390), (450, 480)],  # Friday
}

# Create variables
day = Int('day')
start_time = Int('start_time')

solver = Optimize()

# Constraints on day and start_time
solver.add(And(0 <= day, day <= 4))
solver.add(And(0 <= start_time, start_time <= 450))

# For each day, add constraints that the meeting does not overlap with any busy intervals
for d in range(5):
    # Combine Terry and Frances's busy intervals for the day
    intervals = terry_busy[d] + frances_busy[d]
    for (a, b) in intervals:
        # If the day is d, then the meeting must not overlap with (a, b)
        solver.add(Implies(day == d, Or(start_time + 30 <= a, start_time >= b)))

# Define the priority for the day to prioritize non-Tuesday days first
# Priority mapping: Monday (0) → 0, Tuesday (1) → 4, Wednesday (2) → 1, Thursday (3) → 2, Friday (4) → 3
priority = If(day == 0, 0,
              If(day == 1, 4,
                 If(day == 2, 1,
                    If(day == 3, 2,
                       If(day == 4, 3, 0)))))

solver.minimize(priority)
solver.minimize(start_time)

# Check if solution exists
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_time_val = model[start_time].as_long()
    
    # Convert day to name
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_name = days[day_val]
    
    # Convert start_time to actual time
    start_minutes = start_time_val
    end_minutes = start_minutes + 30
    
    # Convert to hours and minutes
    def format_time(minutes):
        hours = 9 + (minutes // 60)
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_str = format_time(start_minutes)
    end_str = format_time(end_minutes)
    
    print(f"{start_str}:{end_str} {day_name}")
else:
    print("No solution found.")