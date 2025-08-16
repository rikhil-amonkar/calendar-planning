import z3

# Initialize solver
s = z3.Solver()

# Define start time variable (in minutes since midnight)
start = z3.Int('start')

# Add basic constraints for the meeting duration and Helen's cutoff
s.add(start >= 540)  # 9:00 AM
s.add(start <= 870)  # 14:30 PM (meeting ends at 15:00 PM)

# Add constraints for non-overlapping with existing schedules
# Christine's meeting 11:00-11:30 (660-690 minutes)
s.add(z3.Or(start >= 690, start <= 630))

# Helen's blocked time 9:30-10:30 (570-630 minutes)
s.add(z3.Or(start >= 630, start <= 540))

# Helen's blocked time 11:00-11:30 (same as Christine's)
s.add(z3.Or(start >= 690, start <= 630))

# Helen's blocked time 12:00-12:30 (720-750 minutes)
s.add(z3.Or(start >= 750, start <= 690))

# Helen's blocked time 13:30-16:00 (810-960 minutes)
s.add(z3.Or(start >= 960, start <= 780))

# Check for a solution
if s.check() == z3.sat:
    model = s.model()
    start_val = model[start].as_long()
    end_val = start_val + 30

    # Convert minutes to HH:MM format
    def to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time(start_val)}")
    print(f"End Time: {to_time(end_val)}")
else:
    print("No solution found.")