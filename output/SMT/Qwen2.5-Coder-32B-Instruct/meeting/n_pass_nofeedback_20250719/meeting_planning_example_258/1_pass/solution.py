from z3 import *

# Define the locations
locations = ["Embarcadero", "Presidio", "Richmond District", "Fisherman's Wharf"]

# Define the travel times in minutes
travel_times = {
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
}

# Define the people and their availability
people = {
    "Betty": {"location": "Presidio", "start": 10.25, "end": 21.5, "min_meeting": 0.75},
    "David": {"location": "Richmond District", "start": 13.0, "end": 20.25, "min_meeting": 1.5},
    "Barbara": {"location": "Fisherman's Wharf", "start": 9.25, "end": 20.25, "min_meeting": 2.0},
}

# Convert times to minutes from 9:00AM
def time_to_minutes(time):
    return int((time - 9) * 60)

# Create a solver
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {person: Int(f"start_{person}") for person in people}
meeting_end = {person: Int(f"end_{person}") for person in people}

# Define variables for the location at each meeting
meeting_location = {person: String(f"location_{person}") for person in people}

# Add constraints for each person
for person, details in people.items():
    # Meeting must be within the person's availability
    solver.add(meeting_start[person] >= time_to_minutes(details["start"]))
    solver.add(meeting_end[person] <= time_to_minutes(details["end"]))
    # Meeting must be at least the minimum duration
    solver.add(meeting_end[person] - meeting_start[person] >= time_to_minutes(details["min_meeting"]))
    # Meeting must be at the person's location
    solver.add(meeting_location[person] == details["location"])

# Add constraints for travel times
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        # If meeting with person1 ends before meeting with person2 starts, travel time must be considered
        solver.add(Or(meeting_end[person1] + travel_times[(people[person1]["location"], people[person2]["location"])] <= meeting_start[person2],
                      meeting_end[person2] + travel_times[(people[person2]["location"], people[person1]["location"])] <= meeting_start[person1]))

# Add constraint for starting at Embarcadero at 9:00AM
solver.add(meeting_start[list(people.keys())[0]] >= 0)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start_time = model[meeting_start[person]].as_long() / 60 + 9
        end_time = model[meeting_end[person]].as_long() / 60 + 9
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{int(start_time):02}:{int((start_time % 1) * 60):02}",
            "end_time": f"{int(end_time):02}:{int((end_time % 1) * 60):02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")