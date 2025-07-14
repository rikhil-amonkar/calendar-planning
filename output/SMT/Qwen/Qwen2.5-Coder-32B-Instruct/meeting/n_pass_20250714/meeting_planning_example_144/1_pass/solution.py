from z3 import *

# Define the time points in minutes since 9:00 AM
start_time = 0  # 9:00 AM
laura_start = 180  # 12:15 PM
laura_end = 465  # 7:45 PM
anthony_start = 195  # 12:30 PM
anthony_end = 165  # 2:45 PM

# Define the travel times in minutes
travel_times = {
    ('castro', 'mission'): 7,
    ('castro', 'financial'): 20,
    ('mission', 'castro'): 7,
    ('mission', 'financial'): 17,
    ('financial', 'castro'): 23,
    ('financial', 'mission'): 17
}

# Create a solver instance
solver = Solver()

# Define the decision variables
t_castro = Int('t_castro')  # Time spent in The Castro
t_mission = Int('t_mission')  # Time spent in Mission District
t_financial = Int('t_financial')  # Time spent in Financial District

# Define the decision variables for meeting times
meet_laura_start = Int('meet_laura_start')
meet_laura_end = Int('meet_laura_end')
meet_anthony_start = Int('meet_anthony_start')
meet_anthony_end = Int('meet_anthony_end')

# Constraints
solver.add(t_castro >= 0)
solver.add(t_mission >= 0)
solver.add(t_financial >= 0)

# Meeting Laura constraints
solver.add(meet_laura_start >= laura_start)
solver.add(meet_laura_end <= laura_end)
solver.add(meet_laura_end - meet_laura_start >= 75)  # Minimum 75 minutes meeting Laura

# Meeting Anthony constraints
solver.add(meet_anthony_start >= anthony_start)
solver.add(meet_anthony_end <= anthony_end)
solver.add(meet_anthony_end - meet_anthony_start >= 30)  # Minimum 30 minutes meeting Anthony

# Travel constraints
# Assume we start at The Castro at 9:00 AM
current_time = start_time

# Travel to Mission District to meet Laura
current_time += travel_times[('castro', 'mission')]
solver.add(meet_laura_start >= current_time)

# Travel back to The Castro after meeting Laura
current_time = meet_laura_end + travel_times[('mission', 'castro')]

# Travel to Financial District to meet Anthony
current_time += travel_times[('castro', 'financial')]
solver.add(meet_anthony_start >= current_time)

# Travel back to The Castro after meeting Anthony
current_time = meet_anthony_end + travel_times[('financial', 'castro')]

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Meet Laura from {model[meet_laura_start]} to {model[meet_laura_end]}")
    print(f"Meet Anthony from {model[meet_anthony_start]} to {model[meet_anthony_end]}")
else:
    print("No feasible schedule found.")