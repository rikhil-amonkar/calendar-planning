from z3 import *

# Define the locations
locations = ["Fisherman's Wharf", "Bayview", "Golden Gate Park", "Nob Hill", "Marina District", "Embarcadero"]

# Define the travel times in minutes
travel_times = {
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Embarcadero"): 19,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Embarcadero"): 9,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
}

# Define the friends and their availability
friends = {
    "Thomas": {"location": "Bayview", "start": 1530, "end": 1830, "min_duration": 120},
    "Stephanie": {"location": "Golden Gate Park", "start": 1830, "end": 2145, "min_duration": 30},
    "Laura": {"location": "Nob Hill", "start": 845, "end": 1615, "min_duration": 30},
    "Betty": {"location": "Marina District", "start": 1845, "end": 2145, "min_duration": 45},
    "Patricia": {"location": "Embarcadero", "start": 1730, "end": 2200, "min_duration": 45},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {name: Int(f"{name}_start") for name in friends}
meeting_end = {name: Int(f"{name}_end") for name in friends}

# Define variables for the current location at each meeting
current_location = {name: String(f"{name}_location") for name in friends}

# Add constraints for each friend
for name, details in friends.items():
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    location = details["location"]
    
    # Meeting must start after the friend is available and end before the friend leaves
    solver.add(meeting_start[name] >= start_time)
    solver.add(meeting_end[name] <= end_time)
    
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= min_duration)
    
    # Meeting must be at the friend's location
    solver.add(current_location[name] == location)

# Add constraints for travel times
for i, name1 in enumerate(friends):
    for name2 in list(friends.keys())[i+1:]:
        # If meeting with name1 ends before meeting with name2 starts, travel time must be considered
        solver.add(Or(meeting_end[name1] + travel_times[(friends[name1]["location"], friends[name2]["location"])] <= meeting_start[name2],
                      meeting_end[name2] + travel_times[(friends[name2]["location"], friends[name1]["location"])] <= meeting_start[name1]))

# Add constraint for starting at Fisherman's Wharf at 9:00AM
solver.add(meeting_start[list(friends.keys())[0]] >= time_to_minutes(900))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[meeting_start[name]].as_long()
        end = model[meeting_end[name]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start//60:02}:{start%60:02}",
            "end_time": f"{end//60:02}:{end%60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")