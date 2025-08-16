from z3 import Optimize, Int, sat
import json

# Define time constants in minutes after midnight
# 9:00 = 540, 14:15 (2:15PM) = 855, 19:45 (7:45PM) = 1185
ARRIVAL_FW = 540
KENNETH_AVAILABLE_START = 855
KENNETH_AVAILABLE_END = 1185
TRAVEL_TIME_FT_WH_TO_NH = 11

# Create an optimize object
opt = Optimize()

# Define variables (in minutes)
# d_time: the departure time from Fisherman's Wharf
# k_start: meeting start time with Kenneth at Nob Hill
# k_end: meeting end time with Kenneth at Nob Hill
d_time = Int("depart_time")
k_start = Int("kenneth_meet_start")
k_end = Int("kenneth_meet_end")

# Add constraints:
# 1. You cannot leave before you arrive.
opt.add(d_time >= ARRIVAL_FW)
# 2. Kenneth is available at Nob Hill from 14:15 (855) to 19:45 (1185)
opt.add(k_start >= KENNETH_AVAILABLE_START)
opt.add(k_end <= KENNETH_AVAILABLE_END)
# 3. You need to account for travel time from Fisherman's Wharf to Nob Hill.
opt.add(k_start >= d_time + TRAVEL_TIME_FT_WH_TO_NH)
# 4. You want to meet Kenneth for a minimum of 90 minutes.
# For optimal scheduling (to free up time for other friends), we use exactly 90 minutes.
opt.add(k_end - k_start == 90)

# For an optimal schedule (meeting as many friends as possible means not over-allocating time),
# we want the meeting with Kenneth to start as early as possible so you have more time later.
opt.minimize(k_start)

# Check for satisfiability
if opt.check() == sat:
    model = opt.model()
    scheduled_depart = model[d_time].as_long()          # Departure from Fisherman's Wharf
    scheduled_k_start = model[k_start].as_long()          # Meeting start time with Kenneth
    scheduled_k_end = model[k_end].as_long()              # Meeting end time with Kenneth
else:
    raise Exception("No solution found that satisfies the constraints.")

# Function to convert minutes since midnight to "HH:MM" 24-hour format.
def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Prepare the itinerary with a single meeting entry for Kenneth.
itinerary = [
    {
        "action": "meet",
        "person": "Kenneth",
        "start_time": format_time(scheduled_k_start),
        "end_time": format_time(scheduled_k_end)
    }
]

# Output the final itinerary as a JSON-formatted dictionary.
print(json.dumps({"itinerary": itinerary}))