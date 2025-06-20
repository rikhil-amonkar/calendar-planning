from z3 import *

# Define the variables
days_in_vilnius = Int('days_in_vilnius')
days_in_munich = Int('days_in_munich')
days_in_mykonos = Int('days_in_mykonos')
day_in_vilnius = Int('day_in_vilnius')
day_in_munich = Int('day_in_munich')
day_in_mykonos = Int('day_in_mykonos')

# Define the constraints
s = Optimize()
s.add(days_in_vilnius >= 4)
s.add(days_in_munich >= 3)
s.add(days_in_mykonos >= 7)
s.add(days_in_vilnius + days_in_munich + days_in_mykonos == 12)
s.add(day_in_vilnius >= 0)
s.add(day_in_munich >= 0)
s.add(day_in_mykonos >= 0)
s.add(day_in_vilnius <= 4)
s.add(day_in_munich <= 3)
s.add(day_in_mykonos <= 7)
s.add(If(day_in_vilnius > 0, day_in_munich == 0, day_in_munich >= 0))
s.add(If(day_in_munich > 0, day_in_mykonos == 0, day_in_mykonos >= 0))
s.add(If(day_in_mykonos > 0, day_in_vilnius == 0, day_in_vilnius >= 0))

# Solve the optimization problem
s.add(days_in_vilnius + days_in_munich + days_in_mykonos == 12)
solution = s.maximize(days_in_vilnius + days_in_munich + days_in_mykonos)
result = s.check()

if result == sat:
    model = s.model()
    print(f"Days in Vilnius: {model[days_in_vilnius].as_long()}")
    print(f"Days in Munich: {model[days_in_munich].as_long()}")
    print(f"Days in Mykonos: {model[days_in_mykonos].as_long()}")
else:
    print("No solution found")