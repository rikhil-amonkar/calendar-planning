from z3 import *

# Define the variables
days_in_Riga = Int('days_in_Riga')
days_in_Vilnius = Int('days_in_Vilnius')
days_in_Dublin = Int('days_in_Dublin')

# Define the constraints
# Total days should be 12
total_days = days_in_Riga + days_in_Vilnius + days_in_Dublin
s = Solver()
s.add(total_days == 12)

# Days in Riga should be 5
s.add(days_in_Riga == 5)

# Days in Vilnius should be 7
s.add(days_in_Vilnius == 7)

# Days in Dublin should be 2
s.add(days_in_Dublin == 2)

# Check if the solution satisfies all constraints
if s.check() == sat:
    model = s.model()
    print(f"Days in Riga: {model[days_in_Riga].as_long()}")
    print(f"Days in Vilnius: {model[days_in_Vilnius].as_long()}")
    print(f"Days in Dublin: {model[days_in_Dublin].as_long()}")
else:
    print("No solution found")