from z3 import *

# Define the locations and their travel times
locations = ["Presidio", "Richmond District", "North Beach", "Financial District", "Golden Gate Park", "Union Square"]
location_indices = {loc: i for i, loc in enumerate(locations)}
travel_times = {
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Union Square"): 22,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Union Square"): 21,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Union Square"): 7,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Union Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
}

# Define the people and their availability
people = {
    "Jason": {"location": "Richmond District", "start": 13*60, "end": 20*60 + 45, "min_duration": 90},
    "Melissa": {"location": "North Beach", "start": 18*60 + 45, "end": 20*60 + 15, "min_duration": 45},
    "Brian": {"location": "Financial District", "start": 9*60 + 45, "end": 21*60 + 45, "min_duration": 15},
    "Elizabeth": {"location": "Golden Gate Park", "start": 8*60 + 45, "end": 21*60 + 30, "min_duration": 105},
    "Laura": {"location": "Union Square", "start": 14*60 + 15, "end": 19*60 + 30, "min_duration": 75},
}

# Create a solver
solver = Solver()

# Define the start time for each meeting
meeting_starts = {person: Int(f"start_{person}") for person in people}
meeting_ends = {person: Int(f"end_{person}") for person in people}

# Define the location at each meeting as an integer
meeting_locations = {person: Int(f"location_{person}") for person in people}

# Add constraints for each person
for person, details in people.items():
    # Meeting must start after the person is available and end before they are not available
    solver.add(meeting_starts[person] >= details["start"])
    solver.add(meeting_ends[person] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_ends[person] - meeting_starts[person] >= details["min_duration"])
    # Meeting must be at the person's location
    solver.add(meeting_locations[person] == location_indices[details["location"]])

# Function to get travel time between two locations
def get_travel_time(loc1, loc2):
    return travel_times[(locations[loc1], locations[loc2])]

# Add constraints for travel times
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        # If meeting with person1 ends before meeting with person2 starts, travel time must be respected
        travel_time = Int(f"travel_time_{person1}_{person2}")
        solver.add(travel_time == If(meeting_locations[person1] < meeting_locations[person2],
                                    get_travel_time(meeting_locations[person1], meeting_locations[person2]),
                                    get_travel_time(meeting_locations[person2], meeting_locations[person1])))
        solver.add(Or(meeting_ends[person1] + travel_time <= meeting_starts[person2],
                      meeting_ends[person2] + travel_time <= meeting_starts[person1]))

# Add constraint for starting at Presidio at 9:00AM
solver.add(meeting_starts[list(people.keys())[0]] >= 9*60)

# Optimize the schedule to maximize the number of meetings
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(Sum([If(meeting_starts[person] < meeting_ends[person], 1, 0) for person in people]))

# Check if the problem is solvable
if objective.check() == sat:
    model = objective.model()
    itinerary = []
    for person in people:
        start_time = model[meeting_starts[person]].as_long()
        end_time = model[meeting_ends[person]].as_long()
        location_index = model[meeting_locations[person]].as_long()
        if start_time < end_time:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
                "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
            })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")