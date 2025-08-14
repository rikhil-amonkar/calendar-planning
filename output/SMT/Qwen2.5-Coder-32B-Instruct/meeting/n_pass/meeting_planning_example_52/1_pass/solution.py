from z3 import *

# Define the time variables for the meeting with Barbara
barbara_start = Int('barbara_start')
barbara_end = Int('barbara_end')

# Define the constraints
constraints = [
    # Barbara's availability
    barbara_start >= 13 * 60 + 15,  # 1:15 PM in minutes from 00:00
    barbara_end <= 18 * 60 + 15,    # 6:15 PM in minutes from 00:00
    
    # Meeting duration
    barbara_end - barbara_start >= 45,
    
    # Travel time from Russian Hill to Richmond District
    barbara_start >= 9 * 60 + 0 + 14  # 9:00 AM + 14 minutes travel time
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    barbara_start_minutes = model[barbara_start].as_long()
    barbara_end_minutes = model[barbara_end].as_long()
    
    # Convert minutes back to HH:MM format
    def minutes_to_hhmm(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    itinerary = [
        {
            "action": "meet",
            "person": "Barbara",
            "start_time": minutes_to_hhmm(barbara_start_minutes),
            "end_time": minutes_to_hhmm(barbara_end_minutes)
        }
    ]
    
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")