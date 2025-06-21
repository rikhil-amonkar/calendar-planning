from z3 import *

# Define the variables
day = 'Monday'
start_time = 9
end_time = 17
meeting_duration = 30
lisa_busy = [(9, 9.5), (10.5, 11), (14, 16)]
anthony_busy = [(9, 9.5), (11, 11.5), (12.5, 13.5), (14, 15), (15.5, 16), (16.5, 17)]
meeting_start = Real('meeting_start')
meeting_end = Real('meeting_end')

# Create the solver
solver = Solver()

# Add constraints for the day
solver.add(And(meeting_start >= 9, meeting_start <= 17 - meeting_duration))
solver.add(meeting_end >= meeting_start)
solver.add(meeting_end <= 17)

# Add constraints for Lisa's schedule
for start, end in lisa_busy:
    solver.add(Or(meeting_start + meeting_duration < start, meeting_start > end))
    solver.add(Or(meeting_end + meeting_duration < start, meeting_end > end))

# Add constraints for Anthony's schedule
for start, end in anthony_busy:
    solver.add(Or(meeting_start + meeting_duration < start, meeting_start > end))
    solver.add(Or(meeting_end + meeting_duration < start, meeting_end > end))

# Check if a solution exists
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    meeting_start_val = model[meeting_start].as_real().numerator / model[meeting_start].as_real().denominator
    meeting_end_val = model[meeting_end].as_real().numerator / model[meeting_end].as_real().denominator

    # Print the solution
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {int(meeting_start_val):02d}:00")
    print(f"End Time: {int(meeting_end_val):02d}:00")
else:
    print("No solution exists.")