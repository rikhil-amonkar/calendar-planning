from z3 import *

# Define the locations and their travel times
locations = ["Pacific Heights", "North Beach", "Financial District", "Alamo Square", "Mission District"]
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

# Convert times to minutes from start of the day
start_time = 9*60  # 9:00 AM
end_time = 21*60   # 9:00 PM

# Create a solver instance
solver = Solver()

# Define variables for meeting start and end times
meeting_start = {person: Int(f"{person}_start") for person in people}
meeting_end = {person: Int(f"{person}_end") for person in people}

# Define variables for current location
current_location = "Pacific Heights"

# Add constraints for each person
for person, details in people.items():
    # Meeting must start after arrival and end before leaving
    solver.add(meeting_start[person] >= start_time)
    solver.add(meeting_end[person] <= end_time)
    
    # Meeting must be at the person's location
    solver.add(meeting_start[person] >= details["start"])
    solver.add(meeting_end[person] <= details["end"])
    
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[person] - meeting_start[person] >= details["min_duration"])
    
    # Travel time constraints
    if person != "Helen":  # Helen is the first meeting
        prev_person = list(people.keys())[list(people.values()).index(details) - 1]
        solver.add(meeting_start[person] >= meeting_end[prev_person] + travel_times[(people[prev_person]["location"], details["location"])])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start = model[meeting_start[person]].as_long()
        end = model[meeting_end[person]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start//60:02}:{start%60:02}",
            "end_time": f"{end//60:02}:{end%60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No feasible schedule found")