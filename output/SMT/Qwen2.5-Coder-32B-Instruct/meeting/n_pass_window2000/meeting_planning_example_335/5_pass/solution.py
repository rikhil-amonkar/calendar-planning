from z3 import *

# Define the locations
locations = ["Pacific Heights", "North Beach", "Financial District", "Alamo Square", "Mission District"]

# Define the travel times in minutes
travel_times = {
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Mission District"): 15,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Mission District"): 18,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Alamo Square"): 11,
}

# Define the people and their availability
people = {
    "Helen": {"location": "North Beach", "start": 9*60, "end": 17*60, "min_duration": 15},
    "Betty": {"location": "Financial District", "start": 19*60, "end": 21*45, "min_duration": 90},
    "Amanda": {"location": "Alamo Square", "start": 19*45, "end": 21*60, "min_duration": 60},
    "Kevin": {"location": "Mission District", "start": 10*45, "end": 14*45, "min_duration": 45},
}

# Define the start time in minutes from 00:00
start_time = 9*60

# Create a solver
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {person: Int(f"start_{person}") for person in people}
meeting_end = {person: Int(f"end_{person}") for person in people}

# Define variables for the current location
current_location = Int("current_location")

# Add constraints for each person
for person, details in people.items():
    # Meeting must start after the person is available and end before they are not available
    solver.add(meeting_start[person] >= details["start"])
    solver.add(meeting_end[person] <= details["end"])
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[person] - meeting_start[person] >= details["min_duration"])
    # Meeting must be at the person's location
    solver.add(current_location == locations.index(details["location"]))

# Add constraints for travel times
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        # If meeting with person1 ends before meeting with person2 starts, travel time must be considered
        loc1 = people[person1]["location"]
        loc2 = people[person2]["location"]
        travel_time_1_to_2 = travel_times[(loc1, loc2)]
        travel_time_2_to_1 = travel_times[(loc2, loc1)]
        solver.add(Or(meeting_end[person1] + travel_time_1_to_2 <= meeting_start[person2],
                      meeting_end[person2] + travel_time_2_to_1 <= meeting_start[person1]))

# Add constraint for starting location
solver.add(meeting_start["Helen"] >= start_time)  # Start with Helen at 9:00 AM

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, details in people.items():
        start = model[meeting_start[person]].as_long()
        end = model[meeting_end[person]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start//60:02}:{start%60:02}",
            "end_time": f"{end//60:02}:{end%60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")