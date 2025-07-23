from z3 import *

# Define the locations
locations = ["Bayview", "Pacific Heights", "Mission District", "Haight-Ashbury", "Financial District"]

# Define the travel times in minutes
travel_times = {
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Financial District"): 19,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Financial District"): 13,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Financial District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Haight-Ashbury"): 19,
}

# Define the people and their availability
people = {
    "Mary": {"location": "Pacific Heights", "start": 10*60, "end": 19*60, "min_duration": 45},
    "Lisa": {"location": "Mission District", "start": 20*60 + 30, "end": 22*60, "min_duration": 75},
    "Betty": {"location": "Haight-Ashbury", "start": 7*60 + 15, "end": 17*60 + 15, "min_duration": 90},
    "Charles": {"location": "Financial District", "start": 11*60 + 15, "end": 15*60, "min_duration": 120},
}

# Create a solver
solver = Solver()

# Define the start time of the day in minutes (9:00 AM)
start_time = 9 * 60

# Define the variables for the start and end times of each meeting
meeting_starts = {person: Int(f"start_{person}") for person in people}
meeting_ends = {person: Int(f"end_{person}") for person in people}

# Define the location variables for each meeting
meeting_locations = {person: String(f"location_{person}") for person in people}

# Add constraints for each person
for person, details in people.items():
    # Meeting must start after the person is available and end before they are not available
    solver.add(meeting_starts[person] >= details["start"])
    solver.add(meeting_ends[person] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_ends[person] - meeting_starts[person] >= details["min_duration"])
    # Meeting must be at the person's location
    solver.add(meeting_locations[person] == details["location"])

# Add constraints for travel times
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        # If meeting with person1 ends before meeting with person2 starts, travel time must be considered
        solver.add(Or(meeting_ends[person1] + travel_times[(people[person1]["location"], people[person2]["location"])] <= meeting_starts[person2],
                      meeting_ends[person2] + travel_times[(people[person2]["location"], people[person1]["location"])] <= meeting_starts[person1]))

# Add constraint that the first meeting must start after the arrival time
solver.add(meeting_starts[min(people, key=lambda x: people[x]["start"])] >= start_time)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start = model[meeting_starts[person]].as_long()
        end = model[meeting_ends[person]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No feasible schedule found")