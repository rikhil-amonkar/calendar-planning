from z3 import *
import json

# Helper function to convert minutes (after 9:00) into HH:MM 24-hour format.
def to_time(minutes):
    # Our time baseline is 9:00, so add minutes to 9:00.
    total_minutes = 9 * 60 + minutes
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Create a Z3 solver instance.
s = Solver()

# We represent meeting start times as minutes from 9:00.
# Variables:
#   b_start: meeting start with Barbara at Fisherman's Wharf.
#   betty_start: meeting start with Betty at Presidio.
#   d_start: meeting start with David at Richmond District.
b_start = Int("b_start")
betty_start = Int("betty_start")
d_start = Int("d_start")

# Meeting durations (in minutes) as per the requirements.
b_duration = 120  # Barbara for at least 120 minutes.
betty_duration = 45  # Betty for at least 45 minutes.
d_duration = 90   # David for at least 90 minutes.

# Compute end times.
b_end = b_start + b_duration
betty_end = betty_start + betty_duration
d_end = d_start + d_duration

# Friend availability windows (in minutes from 9:00):
# Barbara (Fisherman's Wharf): available 9:15 to 20:15 --> [15, 675]
# Betty (Presidio): available 10:15 to 21:30 --> [75, 750]
# David (Richmond District): available 13:00 to 20:15 --> [240, 675]
s.add(b_start >= 15)
s.add(b_end <= 675)

s.add(betty_start >= 75)
s.add(betty_end <= 750)

s.add(d_start >= 240)
s.add(d_end <= 675)

# Travel constraints between locations (all travel times in minutes):
# Our intended visit order is:
# 1. Start at Embarcadero (arrival at 9:00) 
# 2. Travel to Fisherman's Wharf to meet Barbara.
# 3. Travel to Presidio to meet Betty.
# 4. Travel to Richmond District to meet David.
#
# From Embarcadero to Fisherman's Wharf requires 6 minutes.
# (Since Barbara’s availability starts at 9:15, and 9:00 + 6 = 09:06,
#  the constraint b_start >= 15 is already stricter.)
#
# From Fisherman's Wharf to Presidio requires 17 minutes:
s.add(betty_start >= b_end + 17)

# From Presidio to Richmond District requires 7 minutes:
s.add(d_start >= betty_end + 7)

# Check if a solution exists.
if s.check() == sat:
    m = s.model()
    b_start_val = m[b_start].as_long()
    betty_start_val = m[betty_start].as_long()
    d_start_val = m[d_start].as_long()
    
    b_end_val = b_start_val + b_duration
    betty_end_val = betty_start_val + betty_duration
    d_end_val = d_start_val + d_duration
    
    itinerary = [
        {"action": "meet", "person": "Barbara", "start_time": to_time(b_start_val), "end_time": to_time(b_end_val)},
        {"action": "meet", "person": "Betty",   "start_time": to_time(betty_start_val), "end_time": to_time(betty_end_val)},
        {"action": "meet", "person": "David",   "start_time": to_time(d_start_val), "end_time": to_time(d_end_val)}
    ]
    
    # Output the JSON-formatted itinerary.
    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution found")