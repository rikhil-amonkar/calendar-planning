from z3 import *

# Define the time variables for the meeting with Kenneth
kenneth_start = Int('kenneth_start')
kenneth_end = Int('kenneth_end')

# Define the constraints
constraints = [
    # Kenneth is available from 2:15PM to 7:45PM (14:15 to 19:45 in 24-hour format)
    kenneth_start >= 14 * 60 + 15,  # 2:15PM
    kenneth_end <= 19 * 60 + 45,    # 7:45PM
    # You want to meet Kenneth for at least 90 minutes
    kenneth_end - kenneth_start >= 90,
    # You arrive at Fisherman's Wharf at 9:00AM (09:00 in 24-hour format)
    # Travel time from Fisherman's Wharf to Nob Hill is 11 minutes
    kenneth_start >= 9 * 60 + 0 + 11  # 9:00AM + 11 minutes travel time
]

# Create a solver instance
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    kenneth_start_time = model[kenneth_start].as_long()
    kenneth_end_time = model[kenneth_end].as_long()
    
    # Convert the times back to HH:MM format
    kenneth_start_time_str = f"{kenneth_start_time // 60:02}:{kenneth_start_time % 60:02}"
    kenneth_end_time_str = f"{kenneth_end_time // 60:02}:{kenneth_end_time % 60:02}"
    
    # Create the itinerary
    itinerary = [
        {"action": "meet", "person": "Kenneth", "start_time": kenneth_start_time_str, "end_time": kenneth_end_time_str}
    ]
    
    # Output the result as a JSON-formatted dictionary
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")