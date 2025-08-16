import json
from z3 import Optimize, Int, sat

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create an Optimize object
opt = Optimize()

# Define time in minutes from midnight.
# 9:00AM is 540 minutes, 16:00 is 960 minutes, and 21:45 is 1305 minutes.
departure = Int('departure')  # time to leave Golden Gate Park (in minutes)
meeting_start = Int('meeting_start')  # time at which you start meeting David (in minutes)
meeting_end = Int('meeting_end')      # time at which you finish meeting David (in minutes)

# Constraint: You arrive at Golden Gate Park at 9:00AM so you cannot leave before 540.
opt.add(departure >= 540)

# Travel: It takes 23 minutes to go from Golden Gate Park to Chinatown.
arrival_CT = departure + 23

# Constraint: David is available at Chinatown from 4:00PM (960 minutes) until 9:45PM (1305 minutes)
# and you cannot start meeting him before he arrives.
opt.add(meeting_start >= arrival_CT)
opt.add(meeting_start >= 960)

# Constraint: You want to meet David for at least 105 minutes.
opt.add(meeting_end - meeting_start >= 105)

# Constraint: The meeting must finish as David leaves by 21:45 (1305 minutes).
opt.add(meeting_end <= 1305)

# To free up as much time as possible for meeting other friends (since you are in Golden Gate Park from early on),
# you want to delay your departure from Golden Gate Park as long as possible.
# Note that if you leave too late, you might not get the full 105-minute meeting.
# Given the travel time and minimum meeting duration, departure + 23 + 105 <= 1305,
# so the latest you can leave is 1305 - 128 = 1177 minutes (which is 19:37).
opt.maximize(departure)

# Solve the optimization problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[departure].as_long()  # departure from Golden Gate Park
    s_val = model[meeting_start].as_long()  # meeting start with David
    e_val = model[meeting_end].as_long()  # meeting end with David
    
    # In the optimal solution, we get:
    # d_val = 1177  (i.e. 19:37), so you leave Golden Gate Park at 19:37.
    # Then arriving at Chinatown at 1177+23 = 1200 (i.e. 20:00).
    # Meeting from 20:00 to 20:00+105 = 1305 (i.e. 21:45).
    
    itinerary = [
        {
            "action": "meet",
            "person": "David",
            "start_time": minutes_to_time(s_val),
            "end_time": minutes_to_time(e_val)
        }
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")