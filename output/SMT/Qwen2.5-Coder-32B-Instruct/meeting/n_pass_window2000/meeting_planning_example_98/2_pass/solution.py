from z3 import *

# Define the time variables for each meeting
david_start = Int('david_start')
david_end = Int('david_end')
emily_start = Int('emily_start')
emily_end = Int('emily_end')
frank_start = Int('frank_start')
frank_end = Int('frank_end')

# Define the constraints for each friend's availability
constraints = [
    david_start >= 9 * 60 + 0,  # 9:00 AM in minutes from 00:00
    david_end <= 10 * 60 + 0,   # 10:00 AM in minutes from 00:00
    david_end - david_start >= 30, # Minimum 30 minutes meeting
    
    emily_start >= 11 * 60 + 30,  # 11:30 AM in minutes from 00:00
    emily_end <= 12 * 60 + 30,    # 12:30 PM in minutes from 00:00
    emily_end - emily_start >= 30, # Minimum 30 minutes meeting
    
    frank_start >= 13 * 60 + 0,  # 1:00 PM in minutes from 00:00
    frank_end <= 14 * 60 + 0,    # 2:00 PM in minutes from 00:00
    frank_end - frank_start >= 30, # Minimum 30 minutes meeting
]

# Add constraints to ensure no overlapping meetings
constraints.append(david_end <= emily_start)
constraints.append(emily_end <= frank_start)

# Create a solver instance
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Convert time from minutes to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    itinerary = [
        {
            "action": "meet",
            "person": "David",
            "start_time": format_time(model[david_start].as_long()),
            "end_time": format_time(model[david_end].as_long())
        },
        {
            "action": "meet",
            "person": "Emily",
            "start_time": format_time(model[emily_start].as_long()),
            "end_time": format_time(model[emily_end].as_long())
        },
        {
            "action": "meet",
            "person": "Frank",
            "start_time": format_time(model[frank_start].as_long()),
            "end_time": format_time(model[frank_end].as_long())
        }
    ]
else:
    itinerary = []

# Output the result as a JSON-formatted dictionary
result = {"itinerary": itinerary}
print(result)