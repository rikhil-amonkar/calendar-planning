from z3 import *

# Define the variables
time_start = 9 * 60  # 9:00 AM in minutes
barbara_start = 1 * 60 + 15  # 1:15 PM in minutes
barbara_end = 6 * 60 + 15  # 6:15 PM in minutes
min_meeting_time = 45  # minimum meeting time in minutes
distance_russian_hill_richmond = 14  # travel time from Russian Hill to Richmond District in minutes
distance_richmond_russian_hill = 13  # travel time from Richmond District to Russian Hill in minutes

# Define the solver
s = Optimize()

# Define the variables for the meeting times
meeting_time_russian_hill = Int('meeting_time_russian_hill')
meeting_time_richmond = Int('meeting_time_richmond')

# Define the constraints
s.add(meeting_time_russian_hill >= time_start)
s.add(meeting_time_russian_hill <= barbara_start - min_meeting_time)
s.add(meeting_time_richmond >= barbara_end + min_meeting_time)
s.add(meeting_time_richmond <= 24 * 60 - distance_russian_hill_richmond - distance_richmond_russian_hill)

# Objective function: maximize the meeting time
s.add(Obj('objective', meeting_time_russian_hill + meeting_time_richmond))

# Solve the problem
result = s.check()

# Print the result
if result == sat:
    model = s.model()
    print(f"Best meeting time at Russian Hill: {model[meeting_time_russian_hill] / 60:.0f}:{(model[meeting_time_russian_hill] % 60):02d}")
    print(f"Best meeting time at Richmond District: {model[meeting_time_richmond] / 60:.0f}:{(model[meeting_time_richmond] % 60):02d}")
else:
    print("No solution found")