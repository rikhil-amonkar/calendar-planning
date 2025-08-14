from z3 import *

# Define the time variables for the meeting with Robert
start_meeting = Int('start_meeting')
end_meeting = Int('end_meeting')

# Define the constraints
constraints = [
    # Robert's availability
    start_meeting >= 11 * 60 + 15,  # 11:15AM in minutes
    end_meeting <= 17 * 60 + 45,    # 5:45PM in minutes
    
    # Meeting duration
    end_meeting - start_meeting >= 120,  # At least 120 minutes
    
    # Travel time from Nob Hill to Presidio
    start_meeting >= 9 * 60 + 17,  # 9:00AM + 17 minutes travel time
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[start_meeting].as_long()
    end_time_minutes = model[end_meeting].as_long()
    
    # Convert minutes to HH:MM format
    start_time = f"{start_time_minutes // 60:02}:{start_time_minutes % 60:02}"
    end_time = f"{end_time_minutes // 60:02}:{end_time_minutes % 60:02}"
    
    # Create the itinerary
    itinerary = [
        {"action": "meet", "person": "Robert", "start_time": start_time, "end_time": end_time}
    ]
    
    # Output the result as JSON
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")