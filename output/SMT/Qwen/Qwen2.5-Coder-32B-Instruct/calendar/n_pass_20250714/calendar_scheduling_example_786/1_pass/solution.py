from z3 import *

# Define the days and times
days = ["Monday", "Tuesday", "Wednesday"]
start_times = [9, 9.5, 10, 10.5, 11, 11.5, 12, 12.5, 13, 13.5, 14, 14.5, 15, 15.5, 16, 16.5]
end_times = [t + 0.5 for t in start_times]

# Create a solver instance
solver = Solver()

# Define variables for the day and start time
day_var = Int('day')
start_time_var = Real('start_time')

# Add constraints for the day
solver.add(day_var >= 0)
solver.add(day_var < len(days))

# Add constraints for the start time
solver.add(start_time_var >= 9)
solver.add(start_time_var <= 16.5)

# Convert start_time_var to an index for easier comparison with the list of times
start_time_index = Int('start_time_index')
solver.add(start_time_index == int(start_time_var * 2) - 18)

# Define Amy's busy times
amy_busy_times = {
    "Wednesday": [(11, 11.5), (13.5, 14)]
}

# Define Pamela's busy times
pamela_busy_times = {
    "Monday": [(9, 10.5), (11, 16.5)],
    "Tuesday": [(9, 9.5), (10, 17)],
    "Wednesday": [(9, 9.5), (10, 11), (11.5, 13.5), (14.5, 15), (16, 16.5)]
}

# Add constraints for Amy's availability
for day, busy_periods in amy_busy_times.items():
    if day == days[day_var]:
        for start, end in busy_periods:
            solver.add(Or(start_time_var < start, start_time_var + 0.5 > end))

# Add constraints for Pamela's availability
for day, busy_periods in pamela_busy_times.items():
    if day == days[day_var]:
        for start, end in busy_periods:
            solver.add(Or(start_time_var < start, start_time_var + 0.5 > end))

# Add preference constraint: avoid Monday and Tuesday before 16:00, and Wednesday before 16:00
solver.add(Or(day_var != 0, start_time_var >= 16))
solver.add(Or(day_var != 1, start_time_var >= 16))
solver.add(Or(day_var != 2, start_time_var >= 16))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    day_index = model.evaluate(day_var).as_long()
    start_time = model.evaluate(start_time_var).as_real().numerator() / model.evaluate(start_time_var).as_real().denominator()
    end_time = start_time + 0.5

    # Format the output
    day = days[day_index]
    start_time_str = f"{int(start_time):02}:{int((start_time % 1) * 60):02}"
    end_time_str = f"{int(end_time):02}:{int((end_time % 1) * 60):02}"

    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")