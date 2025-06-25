from z3 import *

# Define the variables
start_time = Int('start_time')
end_time = Int('end_time')
meet_time = Int('meet_time')

# Define the constraints
s = Optimize()
s.add(start_time == 9 * 60)  # Start time is 9:00 AM
s.add(end_time >= start_time + 75)  # Meet Daniel for at least 75 minutes
s.add(meet_time >= start_time + 75)
s.add(meet_time <= 20 * 60)  # Meet Daniel before 8:00 PM
s.add(meet_time % 60 == 0)  # Meet time is in hours
s.add(meet_time >= 7 * 60 + 0)  # Meet Daniel between 7:00 PM and 8:15 PM
s.add(meet_time <= 7 * 60 + 15)  # Meet Daniel between 7:00 PM and 8:15 PM

# Define the travel times
travel_time_richmond_to_russian_hill = 13
travel_time_russian_hill_to_richmond = 14

# Define the objective function
s.add(Obj('total_time', meet_time + travel_time_richmond_to_russian_hill + travel_time_russian_hill_to_richmond))

# Solve the optimization problem
result = s.check()
if result == sat:
    model = s.model()
    print(f"Meet Daniel at {model[meet_time].as_long() // 60} : {model[meet_time].as_long() % 60}")
    print(f"Total time: {model[meet_time].as_long() + travel_time_richmond_to_russian_hill + travel_time_russian_hill_to_richmond} minutes")
else:
    print("No solution found")

SOLUTION: