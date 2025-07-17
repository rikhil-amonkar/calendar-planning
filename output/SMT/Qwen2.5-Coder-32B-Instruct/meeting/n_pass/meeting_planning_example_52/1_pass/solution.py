from z3 import *

# Define the time variables for the meeting with Barbara
barbara_meeting_start = Int('barbara_meeting_start')
barbara_meeting_end = Int('barbara_meeting_end')

# Define the constraints
solver = Solver()

# Constraints for Barbara's meeting
solver.add(barbara_meeting_start >= 13*60 + 15)  # 1:15 PM in minutes
solver.add(barbara_meeting_end <= 18*60 + 15)    # 6:15 PM in minutes
solver.add(barbara_meeting_end - barbara_meeting_start >= 45)  # At least 45 minutes

# Travel time constraints
# Travel from Russian Hill to Richmond District takes 14 minutes
# We start at 9:00 AM (540 minutes)
solver.add(barbara_meeting_start >= 540 + 14)  # We need to account for travel time

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    barbara_start_minutes = model[barbara_meeting_start].as_long()
    barbara_end_minutes = model[barbara_meeting_end].as_long()
    
    # Convert minutes back to HH:MM format
    def minutes_to_hhmm(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    barbara_start_time = minutes_to_hhmm(barbara_start_minutes)
    barbara_end_time = minutes_to_hhmm(barbara_end_minutes)
    
    # Create the itinerary
    itinerary = [
        {"action": "meet", "person": "Barbara", "start_time": barbara_start_time, "end_time": barbara_end_time}
    ]
    
    # Output the result as a JSON-formatted dictionary
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")