from z3 import *
import json

# Helper function to convert minutes since midnight to "HH:MM" 24h format.
def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create an Optimize instance (we could maximize number of meetings; here our constraints force scheduling all three).
opt = Optimize()

# Define the meeting time variables (in minutes since midnight)
# Jason is available at Fisherman's Wharf from 16:00 to 16:45 with a minimum duration of 30 minutes.
jason_start = Int("jason_start")
jason_end = Int("jason_end")
# Jessica is available at Embarcadero from 16:45 to 19:00 with a minimum duration of 30 minutes.
jessica_start = Int("jessica_start")
jessica_end = Int("jessica_end")
# Sandra is available at Richmond District from 18:30 to 21:45 with a minimum duration of 120 minutes.
sandra_start = Int("sandra_start")
sandra_end = Int("sandra_end")

# Define time window constants (in minutes since midnight)
# 9:00 AM is 540 minutes
bayview_arrival = 540
# Jason's window: 16:00 = 960, 16:45 = 1005
jason_window_start = 960
jason_window_end = 1005
# Jessica's window: 16:45 = 1005, 19:00 = 1140
jessica_window_start = 1005
jessica_window_end = 1140
# Sandra's window: 18:30 = 1110, 21:45 = 1305
sandra_window_start = 1110
sandra_window_end = 1305

# Add constraints for Jason's meeting
opt.add(jason_start >= jason_window_start)
opt.add(jason_end <= jason_window_end)
opt.add(jason_end - jason_start >= 30)

# Add constraints for Jessica's meeting
opt.add(jessica_start >= jessica_window_start)
opt.add(jessica_end <= jessica_window_end)
opt.add(jessica_end - jessica_start >= 30)

# Add constraints for Sandra's meeting
opt.add(sandra_start >= sandra_window_start)
opt.add(sandra_end <= sandra_window_end)
opt.add(sandra_end - sandra_start >= 120)

# Travel times between locations (in minutes)
# From Bayview to Fisherman's Wharf: 25 min.
# From Fisherman's Wharf to Embarcadero: 8 min.
# From Embarcadero to Richmond District: 21 min.
travel_bayview_to_fishermans_wharf = 25
travel_fishermans_wharf_to_embarcadero = 8
travel_embarcadero_to_richmond = 21

# Constraint: you start at Bayview at 9:00, so you must account for travel time to reach Jason (Fisherman's Wharf) by his meeting start.
opt.add(bayview_arrival + travel_bayview_to_fishermans_wharf <= jason_start)

# After finishing meeting with Jason at Fisherman's Wharf, you need travel time to get to Embarcadero for Jessica.
opt.add(jason_end + travel_fishermans_wharf_to_embarcadero <= jessica_start)

# After finishing the meeting with Jessica at Embarcadero, account for travel to Richmond District to meet Sandra.
opt.add(jessica_end + travel_embarcadero_to_richmond <= sandra_start)

# (Optional) To encourage early meetings we can set a small objective; here the constraints force the minimum required durations.
# We now check for a valid schedule.
if opt.check() == sat:
    m = opt.model()
    # Retrieve the times from the model.
    jason_start_val = m[jason_start].as_long()
    jason_end_val = m[jason_end].as_long()
    jessica_start_val = m[jessica_start].as_long()
    jessica_end_val = m[jessica_end].as_long()
    sandra_start_val = m[sandra_start].as_long()
    sandra_end_val = m[sandra_end].as_long()

    itinerary = [
        {"action": "meet", "person": "Jason", "start_time": minutes_to_str(jason_start_val), "end_time": minutes_to_str(jason_end_val)},
        {"action": "meet", "person": "Jessica", "start_time": minutes_to_str(jessica_start_val), "end_time": minutes_to_str(jessica_end_val)},
        {"action": "meet", "person": "Sandra", "start_time": minutes_to_str(sandra_start_val), "end_time": minutes_to_str(sandra_end_val)}
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")