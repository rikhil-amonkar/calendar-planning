from z3 import *
import json

# Helper function to convert minutes-since-midnight to HH:MM (24-hour format)
def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour:02d}:{minute:02d}"

# Create an Optimize object so that we can maximize total meeting time.
opt = Optimize()

# Define integer variables representing minutes since midnight.
# For Kenneth (in Mission District)
K_start = Int('K_start')
K_end   = Int('K_end')
# For Thomas (in Pacific Heights)
T_start = Int('T_start')
T_end   = Int('T_end')

# Time constants (in minutes since midnight)
# 9:00 AM = 540 minutes (arrival at Nob Hill)
# Kenneth is available 12:00 - 15:45  => 720 to 945 minutes
# Thomas is available 15:30 - 19:15   => 930 to 1155 minutes
# Minimum meeting durations: Kenneth: 45 minutes, Thomas: 75 minutes.
# Travel times between areas (in minutes):
# Nob Hill -> Mission District: 13
# Mission District -> Pacific Heights: 16
# (Other travel times are not needed since our meeting stops are fixed by friends’ availability)

opt.add(K_start >= 720)         # Kenneth not before 12:00
opt.add(K_end <= 945)           # Kenneth must finish by 15:45
opt.add(K_end - K_start >= 45)  # At least 45 minutes with Kenneth

opt.add(T_start >= 930)         # Thomas not before 15:30
opt.add(T_end <= 1155)          # Thomas must finish by 19:15
opt.add(T_end - T_start >= 75)  # At least 75 minutes with Thomas

# Travel constraint: You finish with Kenneth at Mission District and
# then travel 16 minutes to arrive at Pacific Heights for Thomas.
opt.add(T_start >= K_end + 16)

# Although there is idle time, we want to maximize the total meeting time with both friends.
total_meeting_time = (K_end - K_start) + (T_end - T_start)
h = opt.maximize(total_meeting_time)

# Check for satisfiability and extract the optimal solution.
if opt.check() == sat:
    model = opt.model()
    # Retrieve values from the model (they are in minutes since midnight)
    k_start_val = model[K_start].as_long()
    k_end_val   = model[K_end].as_long()
    t_start_val = model[T_start].as_long()
    t_end_val   = model[T_end].as_long()
    
    # Build the itinerary list with our meeting entries.
    itinerary = [
        {
            "action": "meet",
            "person": "Kenneth",
            "start_time": minutes_to_time(k_start_val),
            "end_time": minutes_to_time(k_end_val)
        },
        {
            "action": "meet",
            "person": "Thomas",
            "start_time": minutes_to_time(t_start_val),
            "end_time": minutes_to_time(t_end_val)
        }
    ]
    
    # Prepare the final result as a JSON-formatted dictionary.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No valid schedule found.")