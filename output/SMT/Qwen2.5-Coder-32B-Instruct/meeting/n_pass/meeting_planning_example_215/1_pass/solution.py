from z3 import *

# Define the locations
locations = ["Bayview", "Embarcadero", "Richmond District", "Fisherman's Wharf"]

# Define the travel times in minutes
travel_times = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Richmond District", "Bayview"): 26,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Richmond District"): 18,
}

# Define the friends and their availability
friends = {
    "Jessica": {"location": "Embarcadero", "start": 1645, "end": 1900, "min_duration": 30},
    "Sandra": {"location": "Richmond District", "start": 1830, "end": 2145, "min_duration": 120},
    "Jason": {"location": "Fisherman's Wharf", "start": 1600, "end": 1645, "min_duration": 30},
}

# Convert times to minutes from 00:00
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Define the start time
start_time = time_to_minutes(900)

# Create a solver
solver = Solver()

# Define the variables for the start and end times of each meeting
meeting_start = {name: Int(f"start_{name}") for name in friends}
meeting_end = {name: Int(f"end_{name}") for name in friends}

# Define the location variables
location = {name: String(f"location_{name}") for name in friends}

# Add constraints for each friend
for name, details in friends.items():
    # Meeting must start after the person is available
    solver.add(meeting_start[name] >= time_to_minutes(details["start"]))
    # Meeting must end before the person is unavailable
    solver.add(meeting_end[name] <= time_to_minutes(details["end"]))
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= details["min_duration"])
    # Meeting must be at the correct location
    solver.add(location[name] == details["location"])

# Add constraints for travel times
for i, name1 in enumerate(friends):
    for name2 in list(friends.keys())[i+1:]:
        # If meeting with name1 ends before meeting with name2 starts, travel from name1's location to name2's location
        solver.add(Or(meeting_end[name1] + travel_times[(friends[name1]["location"], friends[name2]["location"])] <= meeting_start[name2],
                      meeting_end[name2] + travel_times[(friends[name2]["location"], friends[name1]["location"])] <= meeting_start[name1]))

# Add constraint to start at Bayview at 9:00AM
solver.add(meeting_start[list(friends.keys())[0]] >= start_time + travel_times[("Bayview", friends[list(friends.keys())[0]]["location"])])

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
    itinerary.sort(key=lambda x: time_to_minutes(int(x["start_time"].replace(":", ""))))
    print({"itinerary": itinerary})
else:
    print("No solution found")