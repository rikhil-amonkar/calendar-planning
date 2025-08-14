from z3 import *

# Define the locations and their travel times
locations = ["Haight-Ashbury", "Fisherman's Wharf", "Richmond District", "Mission District", "Bayview"]
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
    "Sarah": {"location": "Fisherman's Wharf", "start": 1445, "end": 1730, "min_meeting": 105},
    "Mary": {"location": "Richmond District", "start": 1300, "end": 1915, "min_meeting": 75},
    "Helen": {"location": "Mission District", "start": 2145, "end": 2230, "min_meeting": 30},
    "Thomas": {"location": "Bayview", "start": 1515, "end": 1845, "min_meeting": 120},
}

# Convert times to minutes since start of the day
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Define the start time
start_time = time_to_minutes("09:00")

# Create a solver
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_starts = {name: Int(f"start_{name}") for name in friends}
meeting_ends = {name: Int(f"end_{name}") for name in friends}

# Define variables for the location at each meeting
meeting_locations = {name: String(f"location_{name}") for name in friends}

# Add constraints for each friend
for name, details in friends.items():
    # Meeting must start after the person is available and end before they leave
    solver.add(meeting_starts[name] >= details["start"])
    solver.add(meeting_ends[name] <= details["end"])
    # Meeting must last at least the minimum required time
    solver.add(meeting_ends[name] - meeting_starts[name] >= details["min_meeting"])
    # Meeting must be at the correct location
    solver.add(meeting_locations[name] == details["location"])
    # Meeting times must be within a valid 24-hour period
    solver.add(meeting_starts[name] >= 0)
    solver.add(meeting_starts[name] < 1440)
    solver.add(meeting_ends[name] >= 0)
    solver.add(meeting_ends[name] < 1440)

# Add constraints for travel times
# We will manually order the meetings to ensure feasibility
# Start at Haight-Ashbury at 9:00AM
solver.add(meeting_starts["Mary"] >= start_time + travel_times[("Haight-Ashbury", "Richmond District")])
solver.add(meeting_starts["Thomas"] >= meeting_ends["Mary"] + travel_times[("Richmond District", "Bayview")])
solver.add(meeting_starts["Sarah"] >= meeting_ends["Thomas"] + travel_times[("Bayview", "Fisherman's Wharf")])
solver.add(meeting_starts["Helen"] >= meeting_ends["Sarah"] + travel_times[("Fisherman's Wharf", "Mission District")])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[meeting_starts[name]].as_long()
        end = model[meeting_ends[name]].as_long()
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