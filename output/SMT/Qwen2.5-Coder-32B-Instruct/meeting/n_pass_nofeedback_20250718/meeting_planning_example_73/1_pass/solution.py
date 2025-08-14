from z3 import *

# Define the time variables for the meeting with Barbara
barbara_meeting_start = Int('barbara_meeting_start')
barbara_meeting_end = Int('barbara_meeting_end')

# Define the constraints
constraints = [
    # You arrive at Russian Hill at 9:00AM (540 minutes after midnight)
    barbara_meeting_start >= 540,
    # Barbara is available from 7:15AM (435 minutes after midnight) to 10:00PM (1260 minutes after midnight)
    barbara_meeting_start >= 435,
    barbara_meeting_end <= 1260,
    # You need to meet Barbara for at least 60 minutes
    barbara_meeting_end - barbara_meeting_start >= 60,
    # Travel time from Russian Hill to Pacific Heights is 7 minutes
    # Travel time from Pacific Heights to Russian Hill is 7 minutes
    # Since we start at 9:00AM, we need to account for the travel time if we leave Russian Hill to meet Barbara
    barbara_meeting_start >= 540 + 7
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    barbara_start = model[barbara_meeting_start].as_long()
    barbara_end = model[barbara_meeting_end].as_long()
    
    # Convert the times to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    itinerary = [
        {"action": "meet", "person": "Barbara", "start_time": format_time(barbara_start), "end_time": format_time(barbara_end)}
    ]
    
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")