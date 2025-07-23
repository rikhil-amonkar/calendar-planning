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
    "Karen": {"location": "Nob Hill", "start": 2115, "end": 2145, "min_duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": 1230, "end": 1945, "min_duration": 90},
    "Sandra": {"location": "Chinatown", "start": 715, "end": 1915, "min_duration": 75},
    "Nancy": {"location": "Marina District", "start": 1100, "end": 2015, "min_duration": 105},
}

# Convert times to minutes from 00:00
def time_to_minutes(time):
    return int(str(time)[:2]) * 60 + int(str(time)[2:])

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {person: Int(f"{person}_start") for person in people}
meeting_end = {person: Int(f"{person}_end") for person in people}

# Define the initial location and time
current_location = Int("current_location")
solver.add(current_location == locations.index("Union Square"))

# Add constraints for each person
for person, details in people.items():
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    location_index = locations.index(details["location"])
    
    # Meeting must start within the person's availability
    solver.add(meeting_start[person] >= start_time)
    solver.add(meeting_start[person] <= end_time - min_duration)
    
    # Meeting must end within the person's availability
    solver.add(meeting_end[person] >= meeting_start[person] + min_duration)
    solver.add(meeting_end[person] <= end_time)

# Define the order of meetings and travel times
# We need to ensure that the travel time from the current location to the next location is respected
# We will use a list to keep track of the order of meetings
meeting_order = ["Sandra", "Joseph", "Nancy", "Karen"]  # Example order, needs to be optimized

for i in range(len(meeting_order) - 1):
    prev_person = meeting_order[i]
    person = meeting_order[i + 1]
    prev_location = locations.index(people[prev_person]["location"])
    current_location = locations.index(people[person]["location"])
    solver.add(meeting_end[prev_person] + travel_times[(locations[prev_location], locations[current_location])] <= meeting_start[person])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in meeting_order:
        start = model[meeting_start[person]].as_long()
        end = model[meeting_end[person]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")