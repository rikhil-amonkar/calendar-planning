from z3 import *
import datetime

# Define the travel times between locations (in minutes)
travel_times = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Presidio"): 24,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Union Square"): 22,
}

# Friend information with availability windows
friends = {
    "Richard": {
        "location": "Union Square",
        "available_start": datetime.time(8, 45),
        "available_end": datetime.time(13, 0),
        "min_duration": 120,
    },
    "Charles": {
        "location": "Presidio",
        "available_start": datetime.time(9, 45),
        "available_end": datetime.time(13, 0),
        "min_duration": 120,
    },
}

# Initialize solver
solver = Solver()

# Create variables for meeting times
meetings = {}
for name in friends:
    meetings[name] = {
        "start": Int(f"start_{name}"),
        "end": Int(f"end_{name}"),
    }

# Convert time to minutes since midnight for easier calculations
def time_to_minutes(t):
    return t.hour * 60 + t.minute

# Convert minutes back to time string
def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Add constraints for each meeting
for name, info in friends.items():
    start = meetings[name]["start"]
    end = meetings[name]["end"]
    available_start = time_to_minutes(info["available_start"])
    available_end = time_to_minutes(info["available_end"])
    min_duration = info["min_duration"]

    solver.add(start >= available_start)
    solver.add(end <= available_end)
    solver.add(end - start >= min_duration)
    solver.add(start < end)

# We start at Bayview at 9:00 AM (540 minutes since midnight)
current_time = time_to_minutes(datetime.time(9, 0))
current_location = "Bayview"

# Try both possible meeting orders
order1 = ["Richard", "Charles"]
order2 = ["Charles", "Richard"]

# Function to check a meeting order
def check_order(order):
    temp_solver = Solver()
    temp_solver.add(solver.assertions())
    
    loc = current_location
    time = current_time
    
    for i, name in enumerate(order):
        friend_loc = friends[name]["location"]
        travel = travel_times[(loc, friend_loc)]
        
        # Can't leave before current time
        temp_solver.add(meetings[name]["start"] >= time + travel)
        
        # Update current location and time
        loc = friend_loc
        time = meetings[name]["end"]
        
        # If there's another meeting, add travel time constraint
        if i < len(order) - 1:
            next_name = order[i+1]
            next_loc = friends[next_name]["location"]
            next_travel = travel_times[(loc, next_loc)]
            temp_solver.add(meetings[next_name]["start"] >= time + next_travel)
    
    if temp_solver.check() == sat:
        return temp_solver.model()
    return None

# Try both orders
model = check_order(order1) or check_order(order2)

if model:
    itinerary = []
    for name in friends:
        start = model[meetings[name]["start"]].as_long()
        end = model[meetings[name]["end"]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end),
        })
    
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    
    print('SOLUTION:')
    print({"itinerary": itinerary})
else:
    print("No valid schedule found that meets all constraints")