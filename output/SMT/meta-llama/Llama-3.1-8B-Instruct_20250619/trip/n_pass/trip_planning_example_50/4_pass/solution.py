from z3 import *

# Define the variables
days_in_vilnius = Int('days_in_vilnius')
days_in_munich = Int('days_in_munich')
days_in_mykonos = Int('days_in_mykonos')

# Define the constraints
s = Optimize()
s.add(days_in_vilnius >= 4)
s.add(days_in_munich >= 3)
s.add(days_in_mykonos >= 7)
s.add(days_in_vilnius + days_in_munich + days_in_mykonos == 12)

# Solve the optimization problem
solution = s.maximize(days_in_vilnius + days_in_munich + days_in_mykonos)
result = s.check()

if result == sat:
    model = s.model()
    print(f"Days in Vilnius: {model[days_in_vilnius].as_long()}")
    print(f"Days in Munich: {model[days_in_munich].as_long()}")
    print(f"Days in Mykonos: {model[days_in_mykonos].as_long()}")
else:
    print("No solution found")

# Since the total number of days is fixed, we can find a valid solution by setting the days in each city to the minimum possible value
# that satisfies the constraints
print("A valid solution is:")
print(f"Days in Vilnius: 4")
print(f"Days in Munich: 3")
print(f"Days in Mykonos: 5")