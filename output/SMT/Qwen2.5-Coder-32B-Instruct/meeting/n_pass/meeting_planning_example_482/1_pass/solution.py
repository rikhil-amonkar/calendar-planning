from z3 import *

# Define the locations and their travel times
locations = ["Haight-Ashbury", "Mission District", "Bayview", "Pacific Heights", "Russian Hill", "Fisherman's Wharf"]
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
}

# Define the people and their availability
people = {
    "Stephanie": {"location": "Mission District", "start": 8.25, "end": 13.75, "min_duration": 1.5},
    "Sandra": {"location": "Bayview", "start": 13.0, "end": 19.5, "min_duration": 0.25},
    "Richard": {"location": "Pacific Heights", "start": 7.25, "end": 10.25, "min_duration": 1.25},
    "Brian": {"location": "Russian Hill", "start": 12.25, "end": 16.0, "min_duration": 2.0},
    "Jason": {"location": "Fisherman's Wharf", "start": 8.5, "end": 17.75, "min_duration": 1.0},
}

# Create a solver instance
solver = Solver()

# Define the start time for each person's meeting
meeting_starts = {person: Real(f"start_{person}") for person in people}

# Define the location at each meeting start time
location_at_meeting_start = {person: String(f"loc_{person}") for person in people}

# Define the constraints
for person, details in people.items():
    # Meeting must start within the person's availability
    solver.add(meeting_starts[person] >= details["start"])
    solver.add(meeting_starts[person] <= details["end"] - details["min_duration"])
    
    # Meeting must be at the person's location
    solver.add(location_at_meeting_start[person] == details["location"])

# Define the travel constraints
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        # If person1 meets before person2, the travel time must be considered
        solver.add(Or(meeting_starts[person1] + people[person1]["min_duration"] + travel_times[(location_at_meeting_start[person1], location_at_meeting_start[person2])] <= meeting_starts[person2],
                      meeting_starts[person2] + people[person2]["min_duration"] + travel_times[(location_at_meeting_start[person2], location_at_meeting_start[person1])] <= meeting_starts[person1]))

# Define the initial location and time
initial_location = "Haight-Ashbury"
initial_time = 9.0

# Ensure the first meeting starts after the initial time and at the initial location
first_meeting = min(meeting_starts.values())
solver.add(first_meeting >= initial_time)
solver.add(Or([location_at_meeting_start[person] == initial_location for person in people]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start_time = model[meeting_starts[person]].as_decimal(2)
        end_time = float(start_time) + people[person]["min_duration"]
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{int(start_time):02}:{int((start_time - int(start_time)) * 60):02}",
            "end_time": f"{int(end_time):02}:{int((end_time - int(end_time)) * 60):02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")