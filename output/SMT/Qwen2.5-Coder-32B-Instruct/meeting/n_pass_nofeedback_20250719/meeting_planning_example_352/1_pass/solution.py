from z3 import *

# Define the locations and their travel times
locations = ["Union Square", "Nob Hill", "Haight-Ashbury", "Chinatown", "Marina District"]
travel_times = {
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Marina District"): 18,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Marina District"): 11,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Nob Hill"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Chinatown"): 16,
}

# Define the people and their availability
people = {
    "Karen": {"location": "Nob Hill", "start": 2115, "end": 2145, "min_meeting": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": 1230, "end": 1945, "min_meeting": 90},
    "Sandra": {"location": "Chinatown", "start": 715, "end": 1915, "min_meeting": 75},
    "Nancy": {"location": "Marina District", "start": 1100, "end": 2015, "min_meeting": 105},
}

# Convert times to minutes from 00:00
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_times = {}
for person, details in people.items():
    start = Int(f"{person}_start")
    end = Int(f"{person}_end")
    meeting_times[person] = (start, end)
    solver.add(start >= time_to_minutes(details["start"]))
    solver.add(end <= time_to_minutes(details["end"]))
    solver.add(end - start >= details["min_meeting"])

# Define a variable for the current location
current_location = Int("current_location")
solver.add(current_location == locations.index("Union Square"))

# Define a variable for the current time
current_time = Int("current_time")
solver.add(current_time == time_to_minutes(900))  # Start at 9:00 AM

# Define constraints for each meeting
for person, details in people.items():
    start, end = meeting_times[person]
    location_index = locations.index(details["location"])
    solver.add(current_time + travel_times[(locations[current_location], locations[location_index])] <= start)
    solver.add(current_time + travel_times[(locations[current_location], locations[location_index])] + details["min_meeting"] <= end)
    current_time = end
    current_location = location_index

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, details in people.items():
        start = model[meeting_times[person][0]].as_long()
        end = model[meeting_times[person][1]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")