import z3

# Initialize the Z3 solver
solver = z3.Solver()

# Define the start time variable in minutes since Monday 9:00 AM
start_time = z3.Int('start_time')

# Valid time ranges: Monday (0-450) or Tuesday (480-780)
solver.add(z3.Or(
    z3.And(start_time >= 0, start_time <= 450),
    z3.And(start_time >= 480, start_time <= 780)
))

# Monday constraints: only valid time is 10:00-10:30 AM (60 minutes)
solver.add(z3.Implies(start_time <= 450, start_time == 60))

# Tuesday constraints: avoid blocked intervals
solver.add(z3.Implies(start_time >= 480, z3.And(
    start_time >= 510,  # Avoid 9:00-9:30 AM
    z3.Or(start_time <= 540, start_time >= 600),  # Avoid 10:30-11:30 AM
    z3.Or(start_time <= 660, start_time >= 720)    # Avoid 12:30-13:30 PM
)))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    if time_minutes <= 450:
        # Monday
        day = "Monday"
        hours = 9 + (time_minutes // 60)
        minutes = time_minutes % 60
    else:
        # Tuesday
        day = "Tuesday"
        tuesday_minutes = time_minutes - 480
        hours = 9 + (tuesday_minutes // 60)
        minutes = tuesday_minutes % 60
    
    end_minutes = time_minutes + 30
    end_hours = hours
    end_minutes_val = minutes + 30
    if end_minutes_val >= 60:
        end_hours += 1
        end_minutes_val -= 60
    
    print(f"Start: {day} {hours}:{minutes:02d}, End: {end_hours}:{end_minutes_val:02d}")
else:
    print("No solution found.")