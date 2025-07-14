from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the times you arrive at each location
arrive_nob_hill = Int('arrive_nob_hill')
arrive_pacific_heights = Int('arrive_pacific_heights')
arrive_mission_district = Int('arrive_mission_district')

# Define the travel times (in minutes)
travel_nob_to_pacific = 8
travel_nob_to_mission = 13
travel_pacific_to_nob = 8
travel_pacific_to_mission = 15
travel_mission_to_nob = 12
travel_mission_to_pacific = 16

# Constraints based on arrival time and travel times
solver.add(arrive_nob_hill == 9 * 60)  # Arrive at Nob Hill at 9:00 AM

# Constraints for meeting Kenneth in Mission District
kenneth_start = 12 * 60  # 12:00 PM
kenneth_end = 15 * 60 + 45  # 3:45 PM
kenneth_meeting_time = 45  # Minimum 45 minutes

# Constraint to meet Kenneth
solver.add(arrive_mission_district <= kenneth_start)
solver.add(arrive_mission_district + kenneth_meeting_time <= kenneth_end)

# Constraints for meeting Thomas in Pacific Heights
thomas_start = 15 * 60 + 30  # 3:30 PM
thomas_end = 19 * 60 + 15  # 7:15 PM
thomas_meeting_time = 75  # Minimum 75 minutes

# Constraint to meet Thomas
solver.add(arrive_pacific_heights <= thomas_start)
solver.add(arrive_pacific_heights + thomas_meeting_time <= thomas_end)

# Add constraints for traveling between locations
solver.add(arrive_pacific_heights >= arrive_nob_hill + travel_nob_to_pacific)
solver.add(arrive_mission_district >= arrive_nob_hill + travel_nob_to_mission)
solver.add(arrive_nob_hill >= arrive_pacific_heights + travel_pacific_to_nob)
solver.add(arrive_mission_district >= arrive_pacific_heights + travel_pacific_to_mission)
solver.add(arrive_nob_hill >= arrive_mission_district + travel_mission_to_nob)
solver.add(arrive_pacific_heights >= arrive_mission_district + travel_mission_to_pacific)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Arrive at Nob Hill: {model[arrive_nob_hill].as_long() // 60}:{model[arrive_nob_hill].as_long() % 60:02d} AM")
    print(f"Arrive at Pacific Heights: {model[arrive_pacific_heights].as_long() // 60}:{model[arrive_pacific_heights].as_long() % 60:02d} PM")
    print(f"Arrive at Mission District: {model[arrive_mission_district].as_long() // 60}:{model[arrive_mission_district].as_long() % 60:02d} PM")
else:
    print("No solution found")

# If no solution is found, let's try a different approach to ensure we meet both friends
# We need to ensure that we can reach both locations within the given time constraints
# Let's try a different order of visits

# Reset the solver
solver.reset()

# Define the variables for the times you arrive at each location
arrive_nob_hill = Int('arrive_nob_hill')
arrive_pacific_heights = Int('arrive_pacific_heights')
arrive_mission_district = Int('arrive_mission_district')

# Constraints based on arrival time and travel times
solver.add(arrive_nob_hill == 9 * 60)  # Arrive at Nob Hill at 9:00 AM

# Constraints for meeting Kenneth in Mission District
kenneth_start = 12 * 60  # 12:00 PM
kenneth_end = 15 * 60 + 45  # 3:45 PM
kenneth_meeting_time = 45  # Minimum 45 minutes

# Constraint to meet Kenneth
solver.add(arrive_mission_district <= kenneth_start)
solver.add(arrive_mission_district + kenneth_meeting_time <= kenneth_end)

# Constraints for meeting Thomas in Pacific Heights
thomas_start = 15 * 60 + 30  # 3:30 PM
thomas_end = 19 * 60 + 15  # 7:15 PM
thomas_meeting_time = 75  # Minimum 75 minutes

# Constraint to meet Thomas
solver.add(arrive_pacific_heights <= thomas_start)
solver.add(arrive_pacific_heights + thomas_meeting_time <= thomas_end)

# Add constraints for traveling between locations
solver.add(arrive_mission_district >= arrive_nob_hill + travel_nob_to_mission)
solver.add(arrive_pacific_heights >= arrive_mission_district + travel_mission_to_pacific)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Arrive at Nob Hill: {model[arrive_nob_hill].as_long() // 60}:{model[arrive_nob_hill].as_long() % 60:02d} AM")
    print(f"Arrive at Mission District: {model[arrive_mission_district].as_long() // 60}:{model[arrive_mission_district].as_long() % 60:02d} PM")
    print(f"Arrive at Pacific Heights: {model[arrive_pacific_heights].as_long() // 60}:{model[arrive_pacific_heights].as_long() % 60:02d} PM")
else:
    print("No solution found")