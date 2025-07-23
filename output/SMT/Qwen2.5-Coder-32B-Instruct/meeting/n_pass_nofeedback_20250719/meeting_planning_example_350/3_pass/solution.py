from z3 import *

# Define the locations and their corresponding integer values
locations = {
    "Bayview": 0,
    "Pacific Heights": 1,
    "Mission District": 2,
    "Haight-Ashbury": 3,
    "Financial District": 4
}

# Define the travel times in minutes
travel_times = {
    (0, 1): 23,
    (0, 2): 13,
    (0, 3): 19,
    (0, 4): 19,
    (1, 0): 22,
    (1, 2): 15,
    (1, 3): 11,
    (1, 4): 13,
    (2, 0): 15,
    (2, 1): 16,
    (2, 3): 12,
    (2, 4): 17,
    (3, 0): 18,
    (3, 1): 12,
    (3, 2): 11,
    (3, 4): 21,
    (4, 0): 19,
    (4, 1): 13,
    (4, 2): 17,
    (4, 3): 19,
}

# Define the people and their availability
people = {
    "Mary": {"location": 1, "start": 10*60, "end": 19*60, "min_duration": 45},
    "Lisa": {"location": 2, "start": 20*60 + 30, "end": 22*60, "min_duration": 75},
    "Betty": {"location": 3, "start": 7*60 + 15, "end": 17*60 + 15, "min_duration": 90},
    "Charles": {"location": 4, "start": 11*60 + 15, "end": 15*60, "min_duration": 120},
}

# Create a solver
solver = Solver()

# Define the start time for each person's meeting
meeting_starts = {person: Int(f"start_{person}") for person in people}

# Define the end time for each person's meeting
meeting_ends = {person: Int(f"end_{person}") for person in people}

# Define the location at each meeting start time
location_at_meeting_start = {person: Int(f"loc_start_{person}") for person in people}

# Define the constraints
for person, details in people.items():
    # Meeting must start after the person is available
    solver.add(meeting_starts[person] >= details["start"])
    # Meeting must end before the person is unavailable
    solver.add(meeting_ends[person] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_ends[person] - meeting_starts[person] >= details["min_duration"])
    # Meeting must be at the person's location
    solver.add(location_at_meeting_start[person] == details["location"])

# Define the travel constraints
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        # If meeting with person1 ends before meeting with person2 starts, travel time must be considered
        solver.add(Or(meeting_ends[person1] + travel_times[(location_at_meeting_start[person1], location_at_meeting_start[person2])] <= meeting_starts[person2],
                      meeting_ends[person2] + travel_times[(location_at_meeting_start[person2], location_at_meeting_start[person1])] <= meeting_starts[person1]))

# Define the initial location and start time
initial_location = locations["Bayview"]
initial_time = 9*60

# Add the initial location constraint
solver.add(location_at_meeting_start[list(people.keys())[0]] == initial_location)

# Add the initial time constraint
solver.add(meeting_starts[list(people.keys())[0]] >= initial_time)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start_time = model[meeting_starts[person]].as_long()
        end_time = model[meeting_ends[person]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
            "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
        })
    itinerary = sorted(itinerary, key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")