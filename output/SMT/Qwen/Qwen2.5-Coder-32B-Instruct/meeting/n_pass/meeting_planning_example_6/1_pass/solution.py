from z3 import *

# Define the time variables for each activity
start_meeting_kenneth = Int('start_meeting_kenneth')
end_meeting_kenneth = Int('end_meeting_kenneth')

# Constraints
solver = Solver()

# You arrive at Fisherman's Wharf at 9:00 AM
arrival_time = 9 * 60  # Convert 9:00 AM to minutes

# Kenneth will be at Nob Hill from 2:15 PM to 7:45 PM
kenneth_start = 14 * 60 + 15  # Convert 2:15 PM to minutes
kenneth_end = 19 * 60 + 45    # Convert 7:45 PM to minutes

# Meeting Kenneth for a minimum of 90 minutes
solver.add(end_meeting_kenneth - start_meeting_kenneth >= 90)

# Meeting time must be within Kenneth's availability
solver.add(start_meeting_kenneth >= kenneth_start)
solver.add(end_meeting_kenneth <= kenneth_end)

# Travel time between Fisherman's Wharf and Nob Hill is 11 minutes
travel_time = 11

# Ensure you have enough time to travel to Nob Hill and back
# Assuming you want to start meeting Kenneth as early as possible after arrival
# and return to Fisherman's Wharf by the end of the day (let's assume 11:59 PM)
day_end = 23 * 60 + 59  # Convert 11:59 PM to minutes

# Constraint to ensure you can travel to Nob Hill, meet Kenneth, and return
solver.add(start_meeting_kenneth >= arrival_time + travel_time)
solver.add(end_meeting_kenneth + travel_time <= day_end)

# Objective: Maximize the number of friends met
# For simplicity, let's assume you can meet other friends only when not meeting Kenneth
# and you can meet one friend per hour (60 minutes) excluding travel time

# Define a variable for the number of friends met
num_friends_met = Int('num_friends_met')

# Calculate the available time to meet other friends
available_time = (end_meeting_kenneth - start_meeting_kenneth) - 90  # Time spent with Kenneth minus 90 minutes
available_time += (start_meeting_kenneth - arrival_time - travel_time)  # Time before meeting Kenneth
available_time += (day_end - end_meeting_kenneth - travel_time)  # Time after meeting Kenneth

# You can meet one friend per hour (60 minutes)
solver.add(num_friends_met == available_time // 60)

# Maximize the number of friends met
solver.maximize(num_friends_met)

# Check if the constraints are satisfiable and get the model
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Start meeting Kenneth at: {model[start_meeting_kenneth].as_long() // 60}:{model[start_meeting_kenneth].as_long() % 60:02d}")
    print(f"End meeting Kenneth at: {model[end_meeting_kenneth].as_long() // 60}:{model[end_meeting_kenneth].as_long() % 60:02d}")
    print(f"Number of friends met: {model[num_friends_met]}")
else:
    print("No solution found")