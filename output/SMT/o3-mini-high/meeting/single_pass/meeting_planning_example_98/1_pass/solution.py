from z3 import Solver, Int
import json

def minutes_to_time_str(m):
    # Convert minutes since midnight to HH:MM string in 24-hour format.
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create a Z3 solver instance
s = Solver()

# Define integer variables for the start and end time of the meeting with Timothy (in minutes from midnight)
t_start = Int('t_start')
t_end   = Int('t_end')

# Constants (in minutes)
arrival_time = 9 * 60  # 9:00 AM -> 540 minutes
timothy_avail_start = 20 * 60 + 45  # 8:45 PM -> 1245 minutes
timothy_avail_end   = 21 * 60 + 30    # 9:30 PM -> 1290 minutes
required_duration   = 45             # minimum meeting duration in minutes

travel_AS_to_RD = 12  # Travel time from Alamo Square to Richmond District in minutes
travel_RD_to_AS = 13  # Travel time from Richmond District to Alamo Square in minutes (not used here)

# Add constraints:
# 1. Timothy is available from 20:45 (1245) to 21:30 (1290)
s.add(t_start >= timothy_avail_start)
s.add(t_end <= timothy_avail_end)

# 2. The meeting must last at least 45 minutes.
s.add(t_end - t_start >= required_duration)

# 3. Ensure you can depart Alamo Square after arrival (9:00) and travel (12 minutes) to get there in time.
s.add(t_start >= arrival_time + travel_AS_to_RD)

# Check if the constraints can be satisfied.
if s.check() == 'sat' or s.check().r == 1:
    m = s.model()
    meeting_start = m[t_start].as_long()
    meeting_end   = m[t_end].as_long()
    
    itinerary = [
        {
            "action": "meet",
            "person": "Timothy",
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        }
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")