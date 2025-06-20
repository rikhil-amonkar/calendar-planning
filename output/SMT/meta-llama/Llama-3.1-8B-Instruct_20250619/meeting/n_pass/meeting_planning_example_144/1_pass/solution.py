from z3 import *

# Define the variables
t_castro = Int('t_castro')  # Time spent at The Castro
t_mission = Int('t_mission')  # Time spent at Mission District
t_financial = Int('t_financial')  # Time spent at Financial District

# Define the constraints
s = Optimize()
s.add(t_castro >= 0)  # Time spent at The Castro is non-negative
s.add(t_mission >= 0)  # Time spent at Mission District is non-negative
s.add(t_financial >= 0)  # Time spent at Financial District is non-negative
s.add(t_castro + t_mission + t_financial == 480)  # Total time is 480 minutes (8 hours)
s.add(t_castro >= 90)  # Spend at least 90 minutes at The Castro (from 9:00 AM to 10:30 AM)
s.add(t_castro <= 120)  # Spend no more than 120 minutes at The Castro (from 9:00 AM to 11:00 AM)

# Laura's availability
s.add(And(t_mission >= 45, t_mission <= 270))  # Spend time at Mission District between 12:15 PM and 7:45 PM
s.add(t_mission >= 75)  # Spend at least 75 minutes with Laura

# Anthony's availability
s.add(And(t_financial >= 50, t_financial <= 150))  # Spend time at Financial District between 12:30 PM and 2:45 PM
s.add(t_financial >= 30)  # Spend at least 30 minutes with Anthony

# Travel times
s.add(t_castro + 7 <= t_mission)  # Travel from The Castro to Mission District
s.add(t_mission + 7 <= t_castro + 480)  # Travel from Mission District back to The Castro
s.add(t_castro + 20 <= t_financial)  # Travel from The Castro to Financial District
s.add(t_financial + 17 <= t_castro + 480)  # Travel from Financial District back to The Castro
s.add(t_mission + 17 <= t_financial)  # Travel from Mission District to Financial District
s.add(t_financial + 23 <= t_mission + 480)  # Travel from Financial District back to Mission District

# Solve the optimization problem
solution = s.check()
if solution == sat:
    model = s.model()
    print("Optimal schedule:")
    print(f"Time spent at The Castro: {model[t_castro]} minutes")
    print(f"Time spent at Mission District: {model[t_mission]} minutes")
    print(f"Time spent at Financial District: {model[t_financial]} minutes")
else:
    print("No solution found.")