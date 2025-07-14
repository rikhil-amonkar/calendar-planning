from z3 import *

# Define the possible days and times
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
start_times = [9, 10, 11, 12, 13, 14, 15, 16]
end_times = [10, 11, 12, 13, 14, 15, 16, 17]

# Create a solver instance
solver = Solver()

# Define the variables for the meeting day and time
meeting_day = Int('meeting_day')
meeting_start_time = Int('meeting_start_time')

# Constraints for the meeting day and time
solver.add(meeting_day >= 0)
solver.add(meeting_day < len(days))
solver.add(meeting_start_time >= 9)
solver.add(meeting_start_time < 17)

# Define the constraints based on the availability of Betty and Megan
# Betty's constraints
betty_unavailable = [
    ("Monday", 10, 10.5), ("Monday", 11.5, 12.5), ("Monday", 16, 16.5),
    ("Tuesday", 9.5, 10), ("Tuesday", 10.5, 11), ("Tuesday", 12, 12.5), ("Tuesday", 13.5, 15), ("Tuesday", 16.5, 17),
    ("Wednesday", 13.5, 14), ("Wednesday", 14.5, 15),
    ("Friday", 9, 10), ("Friday", 11.5, 12), ("Friday", 12.5, 13), ("Friday", 14.5, 15)
]

# Megan's constraints
megan_unavailable = [
    ("Monday", 9, 17),
    ("Tuesday", 9, 9.5), ("Tuesday", 10, 10.5), ("Tuesday", 12, 14), ("Tuesday", 15, 15.5), ("Tuesday", 16, 16.5),
    ("Wednesday", 9.5, 10.5), ("Wednesday", 11, 11.5), ("Wednesday", 12.5, 13), ("Wednesday", 13.5, 14.5), ("Wednesday", 15.5, 17),
    ("Thursday", 9, 10.5), ("Thursday", 11.5, 14), ("Thursday", 14.5, 15), ("Thursday", 15.5, 16.5),
    ("Friday", 9, 17)
]

# Add constraints for Betty
for day, start, end in betty_unavailable:
    if day == "Wednesday":
        continue  # Betty cannot meet on Wednesday
    solver.add(Or(meeting_day != days.index(day), meeting_start_time < start, meeting_start_time + 1 > end))

# Add constraints for Megan
for day, start, end in megan_unavailable:
    solver.add(Or(meeting_day != days.index(day), meeting_start_time < start, meeting_start_time + 1 > end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day_value = model[meeting_day].as_long()
    meeting_start_time_value = model[meeting_start_time].as_long()
    meeting_end_time_value = meeting_start_time_value + 1

    print(f"SOLUTION:")
    print(f"Day: {days[meeting_day_value]}")
    print(f"Start Time: {meeting_start_time_value:02}:{'00'}")
    print(f"End Time: {meeting_end_time_value:02}:{'00'}")
else:
    print("No solution found")