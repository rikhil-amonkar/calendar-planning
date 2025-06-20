from z3 import *

# Define the variables
t_castro = Int('t_castro')  # Time spent at The Castro
t_mission = Int('t_mission')  # Time spent at Mission District
t_financial = Int('t_financial')  # Time spent at Financial District
t_laura = Int('t_laura')  # Time spent with Laura
t_anthony = Int('t_anthony')  # Time spent with Anthony

# Define the constraints
s = Optimize()
s.add(t_castro >= 0)  # Time spent at The Castro is non-negative
s.add(t_mission >= 0)  # Time spent at Mission District is non-negative
s.add(t_financial >= 0)  # Time spent at Financial District is non-negative
s.add(t_laura >= 0)  # Time spent with Laura is non-negative
s.add(t_anthony >= 0)  # Time spent with Anthony is non-negative
s.add(t_castro + t_mission + t_financial == 480)  # Total time is 480 minutes (8 hours)
s.add(t_castro >= 90)  # Spend at least 90 minutes at The Castro (from 9:00 AM to 10:30 AM)
s.add(t_castro <= 120)  # Spend no more than 120 minutes at The Castro (from 9:00 AM to 11:00 AM)

# Laura's availability
s.add(And(t_mission >= 45, t_mission <= 270))  # Spend time at Mission District between 12:15 PM and 7:45 PM
s.add(t_laura >= 75)  # Spend at least 75 minutes with Laura
s.add(t_laura <= 300)  # Spend no more than 300 minutes with Laura (5 hours)

# Anthony's availability
s.add(And(t_financial >= 50, t_financial <= 150))  # Spend time at Financial District between 12:30 PM and 2:45 PM
s.add(t_anthony >= 30)  # Spend at least 30 minutes with Anthony
s.add(t_anthony <= 150)  # Spend no more than 150 minutes with Anthony (2.5 hours)

# Travel times
s.add(t_castro + 7 <= t_mission)  # Travel from The Castro to Mission District
s.add(t_mission + 7 <= t_castro + 480)  # Travel from Mission District back to The Castro
s.add(t_castro + 20 <= t_financial)  # Travel from The Castro to Financial District
s.add(t_financial + 17 <= t_castro + 480)  # Travel from Financial District back to The Castro
s.add(t_mission + 17 <= t_financial)  # Travel from Mission District to Financial District
s.add(t_financial + 23 <= t_mission + 480)  # Travel from Financial District back to Mission District

# Meet with exactly 2 people
s.add(Or(t_laura == 0, t_anthony == 0))  # Meet with either Laura or Anthony, but not both

# Solve the optimization problem
solution = s.check()
if solution == sat:
    model = s.model()
    print("Optimal schedule:")
    print(f"Time spent at The Castro: {model[t_castro]} minutes")
    print(f"Time spent at Mission District: {model[t_mission]} minutes")
    print(f"Time spent at Financial District: {model[t_financial]} minutes")
    print(f"Time spent with Laura: {model[t_laura]} minutes")
    print(f"Time spent with Anthony: {model[t_anthony]} minutes")
else:
    print("No solution found.")