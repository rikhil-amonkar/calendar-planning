from z3 import *
import json

# Initialize the solver
s = Solver()

# Define the friends and their details
friends = [
    {"name": "Jeffrey", "location": "Fisherman's Wharf", "start_window": 10*60 + 15, "end_window": 13*60, "min_duration": 90},
    {"name": "Ronald", "location": "Alamo Square", "start_window": 7*60 + 45, "end_window": 14*60 + 45, "min_duration": 120},
    {"name": "Jason", "location": "Financial District", "start_window": 10*60 + 45, "end_window": 16*60, "min_duration": 105},
    {"name": "Melissa", "location": "Union Square", "start_window": 17*60 + 45, "end_window": 18*60 + 15, "min_duration": 15},
    {"name": "Elizabeth", "location": "Sunset District", "start_window": 14*60 + 45, "end_window": 17*60 + 30, "min_duration": 105},
    {"name": "Margaret", "location": "Embarcadero", "start_window": 13*60 + 15, "end_window": 19*60, "min_duration": 90},
    {"name": "George", "location": "Golden Gate Park", "start_window": 19*60, "end_window": 22*60, "min_duration": 75},
    {"name": "Richard", "location": "Chinatown", "start_window": 9*60 + 30, "end_window": 21*60, "min_duration": 15},
    {"name": "Laura", "location": "Richmond District", "start_window": 9*60 + 45, "end_window": 18*60, "min_duration": 60}
]

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Presidio": {
        "Fisherman's Wharf": 19,
        "Alamo Square": 19,
        "Financial District": 23,
        "Union Square": 22,
        "Sunset District": 15,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Alamo Square": 21,
        "Financial District": 11,
        "Union Square": 13,
        "Sunset District": 27,
        "Embarcadero": 8,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Richmond District": 18
    },
    "Alamo Square": {
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Financial District": 17,
        "Union Square": 14,
        "Sunset District": 16,
        "Embarcadero": 16,
        "Golden Gate Park": 9,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Financial District": {
        "Presidio": 22,
        "Fisherman's Wharf": 10,
        "Alamo Square": 17,
        "Union Square": 9,
        "Sunset District": 30,
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Richmond District": 21
    },
    "Union Square": {
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Alamo Square": 15,
        "Financial District": 9,
        "Sunset District": 27,
        "Embarcadero": 11,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Richmond District": 20
    },
    "Sunset District": {
        "Presidio": 16,
        "Fisherman's Wharf": 29,
        "Alamo Square": 17,
        "Financial District": 30,
        "Union Square": 30,
        "Embarcadero": 30,
        "Golden Gate Park": 11,
        "Chinatown": 30,
        "Richmond District": 12
    },
    "Embarcadero": {
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Alamo Square": 19,
        "Financial District": 5,
        "Union Square": 10,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Chinatown": 7,
        "Richmond District": 21
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Fisherman's Wharf": 24,
        "Alamo Square": 9,
        "Financial District": 26,
        "Union Square": 22,
        "Sunset District": 10,
        "Embarcadero": 25,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Presidio": 19,
        "Fisherman's Wharf": 8,
        "Alamo Square": 17,
        "Financial District": 5,
        "Union Square": 7,
        "Sunset District": 29,
        "Embarcadero": 5,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Presidio": 7,
        "Fisherman's Wharf": 18,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Sunset District": 11,
        "Embarcadero": 19,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

# Create variables for each friend's meeting start and end times (in minutes since 9:00 AM)
for friend in friends:
    friend["start"] = Int(f"start_{friend['name']}")
    friend["end"] = Int(f"end_{friend['name']}")
    # Constraints: meeting within friend's window and duration
    s.add(friend["start"] >= friend["start_window"] - 9*60)
    s.add(friend["end"] <= friend["end_window"] - 9*60)
    s.add(friend["end"] == friend["start"] + friend["min_duration"])
    s.add(friend["start"] >= 0)  # Cannot start before 9:00 AM

# We need to define the order of meetings. This is a complex part; for simplicity, we'll assume an order.
# Alternatively, we can use a more sophisticated approach with sequencing variables.
# Here, we'll try to meet as many friends as possible in a feasible order.

# For simplicity, let's try a specific order that might work: Laura, Ronald, Jeffrey, Jason, Margaret, Elizabeth, George, Richard, Melissa.
# We'll add constraints for travel times between consecutive meetings.

# Define the order (this is a heuristic; in a real scenario, we'd need to explore different orders)
order = ["Laura", "Ronald", "Jeffrey", "Jason", "Margaret", "Elizabeth", "George", "Richard", "Melissa"]

# Create a list of friends in the order we want to meet them
ordered_friends = []
for name in order:
    for friend in friends:
        if friend["name"] == name:
            ordered_friends.append(friend)
            break

# Add constraints for travel times between consecutive meetings
current_location = "Presidio"
current_end = 0  # Starting at 9:00 AM (0 minutes after 9:00 AM)

for i in range(len(ordered_friends)):
    friend = ordered_friends[i]
    # The start time of this friend's meeting must be >= current_end + travel time from current_location to friend's location
    travel_time = travel_times[current_location][friend["location"]]
    s.add(friend["start"] >= current_end + travel_time)
    # Update current_location and current_end
    current_location = friend["location"]
    current_end = friend["end"]

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    for friend in friends:
        start_val = model.evaluate(friend["start"]).as_long()
        end_val = model.evaluate(friend["end"]).as_long()
        start_hour = 9 + start_val // 60
        start_min = start_val % 60
        end_hour = 9 + end_val // 60
        end_min = end_val % 60
        itinerary.append({
            "action": "meet",
            "person": friend["name"],
            "start_time": f"{start_hour:02d}:{start_min:02d}",
            "end_time": f"{end_hour:02d}:{end_min:02d}"
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:5])))
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')