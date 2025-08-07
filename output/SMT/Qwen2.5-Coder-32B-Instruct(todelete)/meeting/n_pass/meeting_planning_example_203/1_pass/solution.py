from z3 import *

# Define the locations and their travel times
locations = ["Financial District", "Fisherman's Wharf", "Pacific Heights", "Mission District"]
travel_times = {
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Pacific Heights"): 16,
}

# Define the people and their availability
people = {
    "David": {"location": "Fisherman's Wharf", "start": 10.75, "end": 15.5, "min_meeting": 0.25},
    "Timothy": {"location": "Pacific Heights", "start": 9.0, "end": 15.5, "min_meeting": 1.25},
    "Robert": {"location": "Mission District", "start": 12.25, "end": 19.75, "min_meeting": 1.5},
}

# Convert times to minutes from 9:00AM
def time_to_minutes(time):
    return int((time - 9) * 60)

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {person: Int(f"start_{person}") for person in people}
meeting_end = {person: Int(f"end_{person}") for person in people}

# Define variables for the current location at each meeting
current_location = {person: String(f"location_{person}") for person in people}

# Add constraints for each person
for person, details in people.items():
    # Meeting must start after the person is available and end before they leave
    solver.add(meeting_start[person] >= time_to_minutes(details["start"]))
    solver.add(meeting_end[person] <= time_to_minutes(details["end"]))
    # Meeting must last at least the minimum required time
    solver.add(meeting_end[person] - meeting_start[person] >= time_to_minutes(details["min_meeting"]))
    # Meeting must be at the person's location
    solver.add(current_location[person] == details["location"])

# Add constraints for travel times
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        # If meeting with person1 ends before meeting with person2 starts, travel time must be considered
        solver.add(Or(meeting_end[person1] + travel_times[(current_location[person1], current_location[person2])] <= meeting_start[person2],
                      meeting_end[person2] + travel_times[(current_location[person2], current_location[person1])] <= meeting_start[person1]))

# Add constraint for starting at Financial District at 9:00AM
solver.add(current_location["Timothy"] == "Pacific Heights")  # Timothy is the first person we meet, starting at 9:00AM

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start_time = model[meeting_start[person]].as_long()
        end_time = model[meeting_end[person]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{9 + start_time // 60:02}:{start_time % 60:02}",
            "end_time": f"{9 + end_time // 60:02}:{end_time % 60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")