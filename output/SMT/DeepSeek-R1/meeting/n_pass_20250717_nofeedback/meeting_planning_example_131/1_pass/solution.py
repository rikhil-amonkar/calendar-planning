from z3 import *
import json

def min_to_time(total_minutes):
    base_hour = 9
    hours = base_hour + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Create solver
s = Solver()

# Define variables for meeting start times (in minutes from 9:00 AM)
jason_start = Int('jason_start')
kenneth_start = Int('kenneth_start')

# Fixed meeting durations
jason_duration = 90
kenneth_duration = 45

# End times and travel
jason_end = jason_start + jason_duration
arrival_marina = jason_end + 10  # travel time from Presidio to Marina is 10 minutes
kenneth_end = kenneth_start + kenneth_duration

# Constraints for Jason:
#   - Available from 10:00 AM (60 minutes) to 4:15 PM (435 minutes), but we require end by 3:50 PM (410 minutes) to have time for Kenneth.
s.add(jason_start >= 60)        # cannot start before Jason is available
s.add(jason_end <= 410)         # must leave Presidio by 3:50 PM to have time for Kenneth

# Constraints for Kenneth:
#   - Available from 3:30 PM (390 minutes) to 4:45 PM (465 minutes)
s.add(kenneth_start >= 390)     # cannot start before Kenneth is available
s.add(kenneth_end <= 465)       # must end by 4:45 PM

# Travel constraint: we must arrive at Marina before we can start meeting Kenneth
s.add(kenneth_start >= arrival_marina)

# Check and get the model
if s.check() == sat:
    m = s.model()
    js_val = m[jason_start].as_long()
    ks_val = m[kenneth_start].as_long()
    je_val = js_val + jason_duration
    ke_val = ks_val + kenneth_duration

    # Convert to time strings
    jason_start_time = min_to_time(js_val)
    jason_end_time = min_to_time(je_val)
    kenneth_start_time = min_to_time(ks_val)
    kenneth_end_time = min_to_time(ke_val)

    itinerary = [
        {"action": "meet", "person": "Jason", "start_time": jason_start_time, "end_time": jason_end_time},
        {"action": "meet", "person": "Kenneth", "start_time": kenneth_start_time, "end_time": kenneth_end_time}
    ]

    # Output the solution in the required format
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")