from z3 import *

# Define the variables for the day and time
day = Int('day')
start_time = Int('start_time')

# Define the domain for the variables
days = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2, 'Thursday': 3, 'Friday': 4}
day_values = list(days.values())
day_names = list(days.keys())

# Define the constraints for Diane and Matthew
diane_busy_times = {
    0: [(12*60, 12*60+30), (15*60, 15*60+30)],
    1: [(10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), (16*60, 17*60)],
    2: [(9*60, 9*60+30), (14*60+30, 15*60), (16*60+30, 17*60)],
    3: [(15*60+30, 16*60+30)],
    4: [(9*60+30, 11*60+30), (14*60+30, 15*60), (16*60, 17*60)]
}

matthew_busy_times = {
    0: [(9*60, 10*60), (10*60+30, 17*60)],
    1: [(9*60, 17*60)],
    2: [(9*60, 11*60), (12*60, 14*60+30), (16*60, 17*60)],
    3: [(9*60, 16*60)],
    4: [(9*60, 17*60)]
}

# Create a solver instance
solver = Solver()

# Add constraints for valid day and time
solver.add(day >= 0)
solver.add(day <= 4)
solver.add(start_time >= 9*60)
solver.add(start_time + 60 <= 17*60)

# Add constraints for Diane's busy times
for d, times in diane_busy_times.items():
    for start, end in times:
        solver.add(Or(day != d, Or(start_time >= end, start_time + 60 <= start)))

# Add constraints for Matthew's busy times
for d, times in matthew_busy_times.items():
    for start, end in times:
        solver.add(Or(day != d, Or(start_time >= end, start_time + 60 <= start)))

# Add constraint for Matthew's preference
solver.add(Or(day != 2, start_time >= 12*60+30))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = day_names[model[day].as_long()]
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + 60

    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time//60}:{meeting_start_time%60:02}\nEnd Time: {meeting_end_time//60}:{meeting_end_time%60:02}")
else:
    print("No solution found")