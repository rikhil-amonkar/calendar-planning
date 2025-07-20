from z3 import *

# Define the locations
locations = ["Haight-Ashbury", "Fisherman's Wharf", "Richmond District", "Mission District", "Bayview"]

# Define the travel times in minutes
travel_times = {
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Bayview"): 26,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Bayview"): 15,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Mission District"): 13,
}

# Define the friends and their availability
friends = {
    "Sarah": {"location": "Fisherman's Wharf", "start": 1445, "end": 1730, "min_duration": 105},
    "Mary": {"location": "Richmond District", "start": 1300, "end": 1915, "min_duration": 75},
    "Helen": {"location": "Mission District", "start": 2145, "end": 2230, "min_duration": 30},
    "Thomas": {"location": "Bayview", "start": 1515, "end": 1845, "min_duration": 120},
}

# Convert times to minutes since 00:00
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Define the start time
start_time = time_to_minutes("09:00")

# Create a solver
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {name: Int(f"start_{name}") for name in friends}
meeting_end = {name: Int(f"end_{name}") for name in friends}

# Define variables for the location at each meeting
meeting_location = {name: String(f"location_{name}") for name in friends}

# Add constraints for each friend
for name, details in friends.items():
    # Meeting must start after the person is available
    solver.add(meeting_start[name] >= details["start"])
    # Meeting must end before the person is unavailable
    solver.add(meeting_end[name] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= details["min_duration"])
    # Meeting must be at the correct location
    solver.add(meeting_location[name] == details["location"])

# Add constraints for travel times
for i, name1 in enumerate(friends):
    for name2 in list(friends.keys())[i+1:]:
        # If meeting with name1 ends before meeting with name2 starts, travel time must be considered
        solver.add(Or(meeting_end[name1] + travel_times[(friends[name1]["location"], friends[name2]["location"])] <= meeting_start[name2],
                      meeting_end[name2] + travel_times[(friends[name2]["location"], friends[name1]["location"])] <= meeting_start[name1]))

# Add constraint for starting at Haight-Ashbury at 9:00AM
solver.add(meeting_start[list(friends.keys())[0]] >= start_time + travel_times[("Haight-Ashbury", friends[list(friends.keys())[0]]["location"])])

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
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    print({"itinerary": itinerary})
else:
    print("No solution found")