from z3 import Optimize, Int, sat
import json

def convert_time(minutes):
    """Convert minutes since midnight into HH:MM (24-hour) format."""
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Create an optimization object so we can maximize total meeting time.
opt = Optimize()

# Define our integer variables (representing minutes since midnight)
# Jason meeting start and end times, and Kenneth meeting start and end times.
J_start = Int('J_start')  # Jason meeting start time
J_end   = Int('J_end')    # Jason meeting end time
K_start = Int('K_start')  # Kenneth meeting start time
K_end   = Int('K_end')    # Kenneth meeting end time

# Define constant times (in minutes since midnight)
PH_arrival   = 9 * 60          # 9:00 AM => 540
J_avail_start = 10 * 60         # 10:00 AM => 600
J_avail_end   = 16 * 60 + 15    # 16:15 => 975
K_avail_start = 15 * 60 + 30    # 15:30 => 930
K_avail_end   = 16 * 60 + 45    # 16:45 => 1005

# Travel times in minutes
PH_to_Presidio      = 11       # Pacific Heights to Presidio
Presidio_to_Marina  = 10       # Presidio to Marina District
# (Other travel distances are given but for this schedule only these two legs matter.)

# Add constraints for Jason's meeting:
# 1. You can't start meeting Jason before he is available and before arriving in Presidio.
opt.add(J_start >= J_avail_start)
opt.add(J_start >= PH_arrival + PH_to_Presidio)  # Must allow travel from Pacific Heights

# 2. The meeting must last at least 90 minutes and finish by his availability end.
opt.add(J_end - J_start >= 90)
opt.add(J_end <= J_avail_end)

# Add constraints for Kenneth's meeting:
# 1. Kenneth is available only from 15:30 to 16:45.
opt.add(K_start >= K_avail_start)
opt.add(K_end <= K_avail_end)
# 2. Meeting time must be at least 45 minutes.
opt.add(K_end - K_start >= 45)

# Travel constraint between meetings:
# After finishing with Jason in Presidio, you must travel to Marina District (10 minutes) to start Kenneth's meeting.
opt.add(J_end + Presidio_to_Marina <= K_start)

# To “optimize your goals”, we want to maximize the total meeting time with friends.
total_meeting_time = (J_end - J_start) + (K_end - K_start)
opt.maximize(total_meeting_time)

# Check for an optimal solution.
if opt.check() == sat:
    model = opt.model()
    j_s = model[J_start].as_long()
    j_e = model[J_end].as_long()
    k_s = model[K_start].as_long()
    k_e = model[K_end].as_long()

    itinerary = [
        {
            "action": "meet",
            "person": "Jason",
            "start_time": convert_time(j_s),
            "end_time": convert_time(j_e)
        },
        {
            "action": "meet",
            "person": "Kenneth",
            "start_time": convert_time(k_s),
            "end_time": convert_time(k_e)
        }
    ]
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=4))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}, indent=4))