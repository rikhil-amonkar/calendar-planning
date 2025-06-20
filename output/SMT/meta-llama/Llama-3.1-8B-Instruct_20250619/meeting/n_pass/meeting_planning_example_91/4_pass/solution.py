from z3 import *

# Define the variables
start_time = Int('start_time')
end_time = Int('end_time')
richmond_time = Int('richmond_time')
meet_daniel = Bool('meet_daniel')
meet_other = Bool('meet_other')

# Define the constraints
s = Optimize()
s.add(9 <= start_time)  # You arrive at Russian Hill at 9:00AM
s.add(start_time <= end_time)  # You need to meet Daniel before the end of the day
s.add(end_time <= 20)  # You need to end the day by 8:15PM
s.add(7 * 60 <= richmond_time)  # Daniel will be at Richmond District from 7:00PM
s.add(richmond_time <= 8 * 60 + 15)  # Daniel will be at Richmond District until 8:15PM
s.add(meet_daniel == (richmond_time - start_time >= 75))  # You'd like to meet Daniel for a minimum of 75 minutes
s.add(meet_other == (end_time - start_time >= 60))  # You'd like to meet another person for a minimum of 60 minutes
s.add(meet_daniel + meet_other == 1)  # You can meet either Daniel or another person
s.add(If(meet_daniel, richmond_time - start_time >= 75, False).as_bool())  # You'd like to meet Daniel for a minimum of 75 minutes
s.add(If(meet_other, end_time - start_time >= 60, False).as_bool())  # You'd like to meet another person for a minimum of 60 minutes

# Define the objective function
s.minimize(end_time)

# Solve the optimization problem
opt_result = s.check()
if opt_result == sat:
    opt_model = s.model()
    print(f"Start time: {opt_model[start_time].as_long()}")
    print(f"End time: {opt_model[end_time].as_long()}")
    print(f"Richmond time: {opt_model[richmond_time].as_long()}")
    print(f"Meet Daniel: {opt_model[meet_daniel].as_bool()}")
    print(f"Meet other: {opt_model[meet_other].as_bool()}")
else:
    print("No solution found")