from z3 import *

# Define the variables
time = Int('time')
arrive_alamo_square = 9 * 60  # 9:00 AM in minutes
timothy_arrive = 8 * 60 + 45  # 8:45 PM in minutes
timothy_leave = 21 * 60  # 9:30 PM in minutes
min_meeting_time = 45  # 45 minutes
travel_time_alamo_to_richmond = 12
travel_time_richmond_to_alamo = 13

# Define the constraints
s = Optimize()

# Decision variables
visit_richmond = Bool('visit_richmond')
start_time_richmond = If(visit_richmond, time, 0)

# Constraints
s.add(And(time >= arrive_alamo_square,
         time >= 0,
         time <= timothy_leave,
         time + min_meeting_time <= timothy_leave,
         If(visit_richmond, time + travel_time_alamo_to_richmond, 0) <= timothy_arrive,
         If(visit_richmond, time + travel_time_alamo_to_richmond + min_meeting_time, 0) <= timothy_leave))

# Objective function
s.maximize(If(visit_richmond, 1, 0))

# Solve the problem
solution = s.check()

if solution == sat:
    model = s.model()
    print("Best schedule:")
    print(f"Visit Richmond District: {model[visit_richmond]}")
    print(f"Start time in Richmond District: {model[start_time_richmond].as_long()} minutes")
    total_time = model[start_time_richmond].as_long() + travel_time_alamo_to_richmond + min_meeting_time
    print(f"Total time in Richmond District: {total_time} minutes")
else:
    print("No solution found")