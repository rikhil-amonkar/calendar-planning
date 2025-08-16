import json
from z3 import *

def minutes_to_str(m):
    """Converts minutes past midnight to HH:MM 24-hour format."""
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Create a Z3 solver instance
s = Solver()

# Constants (times in minutes from midnight)
arrival_russian_hill = 9 * 60         # 9:00 AM -> 540 minutes
travel_rh_to_ph = 7                  # 7 minutes travel time from Russian Hill to Pacific Heights
min_meet_duration = 60               # Must meet Barbara for at least 60 minutes

# Barbara’s availability at Pacific Heights:
barbara_available_start = 7 * 60 + 15  # 7:15 AM -> 435 minutes
barbara_available_end = 22 * 60        # 10:00 PM -> 1320 minutes

# Variables for the meeting with Barbara (times in minutes from midnight)
meet_start = Int('meet_start')
meet_end = Int('meet_end')

# Constraint 1: You must travel from Russian Hill, so you can't start before 9:00 + 7 = 9:07
s.add(meet_start == arrival_russian_hill + travel_rh_to_ph)

# Constraint 2: Your meeting must occur when Barbara is available.
s.add(meet_start >= barbara_available_start)
s.add(meet_end <= barbara_available_end)

# Constraint 3: The meeting duration must be at least 60 minutes.
s.add(meet_end == meet_start + min_meet_duration)

# For this simplified scenario (maximizing friends met), we assume that meeting Barbara is the only friend scheduled.
# In a more complex scenario, you would add more meeting variables with their travel and duration constraints.
if s.check() == sat:
    model = s.model()
    start_time = model[meet_start].as_long()
    end_time = model[meet_end].as_long()
    
    itinerary = [
        {
            "action": "meet",
            "person": "Barbara",
            "start_time": minutes_to_str(start_time),
            "end_time": minutes_to_str(end_time)
        }
    ]
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=4))
else:
    print("No solution exists.")
    
if __name__ == "__main__":
    pass