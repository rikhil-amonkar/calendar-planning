from z3 import *

# Define the time variables for the start and end of the meeting with Robert
start_meeting = Int('start_meeting')
end_meeting = Int('end_meeting')

# Define the constraints
constraints = [
    # Robert's availability
    start_meeting >= 11 * 60 + 15,  # 11:15AM in minutes
    end_meeting <= 17 * 60 + 45,    # 5:45PM in minutes
    
    # Meeting duration
    end_meeting - start_meeting >= 120,  # At least 120 minutes
    
    # Ensure start_meeting and end_meeting are valid times
    start_meeting >= 0,
    end_meeting >= 0,
    start_meeting < end_meeting
]

# Create a solver instance
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
    
    # Output the result as a JSON-formatted dictionary
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")