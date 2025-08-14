from z3 import *

# Define the time points in minutes since 9:00 AM
start_time = 0  # 9:00 AM
laura_start = 180  # 12:15 PM
laura_end = 465  # 7:45 PM
anthony_start = 195  # 12:30 PM
anthony_end = 285  # 2:45 PM

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

# Define the decision variables for meeting times
meet_laura_start = Int('meet_laura_start')
meet_laura_end = Int('meet_laura_end')
meet_anthony_start = Int('meet_anthony_start')
meet_anthony_end = Int('meet_anthony_end')

# Meeting Laura constraints
solver.add(meet_laura_start == 180)  # Start at 12:15 PM
solver.add(meet_laura_end == 255)  # End at 1:15 PM
solver.add(meet_laura_end - meet_laura_start >= 75)  # Minimum 75 minutes meeting Laura

# Meeting Anthony constraints
solver.add(meet_anthony_start == 282)  # Start at 1:42 PM
solver.add(meet_anthony_end == 312)  # End at 2:12 PM
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

# Ensure the schedule is feasible
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    def convert_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    meet_laura_start_time = convert_to_time(model[meet_laura_start].as_long())
    meet_laura_end_time = convert_to_time(model[meet_laura_end].as_long())
    meet_anthony_start_time = convert_to_time(model[meet_anthony_start].as_long())
    meet_anthony_end_time = convert_to_time(model[meet_anthony_end].as_long())
    
    print(f"Meet Laura from {meet_laura_start_time} to {meet_laura_end_time}")
    print(f"Meet Anthony from {meet_anthony_start_time} to {meet_anthony_end_time}")
else:
    print("No feasible schedule found.")