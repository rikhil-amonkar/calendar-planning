import z3

# Define variables
day = z3.Int('day')
start_time = z3.Int('start_time')
end_time = z3.Int('end_time')

# Initialize the Z3 optimizer
opt = z3.Optimize()

# Constraint: Day must be between 2 and 4 (Tuesday to Thursday)
opt.add(z3.And(2 <= day, day <= 4))

# Constraint: If the day is Tuesday (2), the time must be 9:30 to 10:30
opt.add(z3.Implies(
    day == 2,
    z3.And(start_time == 570, end_time == 630)
))

# Constraint: If the day is Wednesday (3), the meeting must not be between 9:00 and 11:30 (540 to 690 minutes)
opt.add(z3.Implies(
    day == 3,
    z3.Or(end_time <= 540, start_time >= 690)
))

# Optional: Ensure that start_time is less than end_time
opt.add(start_time < end_time)

# Preference: Minimize the day to prefer earlier days
opt.minimize(day)

# Check for a solution
if opt.check() == z3.sat:
    model = opt.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    end_val = model[end_time].as_long()

    # Convert minutes back to time format for output
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    start_time_str = minutes_to_time(start_val)
    end_time_str = minutes_to_time(end_val)

    print(f"Solution: day = {day_val}, time_range = {{{start_time_str}:{end_time_str}}}")
else:
    print("No solution found.")