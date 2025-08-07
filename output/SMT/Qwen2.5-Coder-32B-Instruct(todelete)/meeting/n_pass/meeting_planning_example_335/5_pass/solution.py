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

# Convert times to minutes from start of the0 day
start_time = 9*60  # 9:00 AM
end_time = 21*60   # 9:00 PM

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_vars = {}
for person, details in people.items():
    start = Int(f"{person}_start")
    end = Int(f"{person}_end")
    meeting_vars[person] = (start, end)
    solver.add(start >= start_time)
    solver.add(end <= end_time)
    solver.add(end - start >= details["min_duration"])
    solver.add(start >= details["start"])
    solver.add(end <= details["end"])

# Define the initial location and time
current_location = "Pacific Heights"
current_time = start_time

# Add constraints for each meeting
for person, details in people.items():
    start, end = meeting_vars[person]
    solver.add(start >= current_time + travel_times[(current_location, details["location"])])
    # Update current location and time after meeting
    current_location = details["location"]
    current_time = end

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, details in people.items():
        start = model[meeting_vars[person][0]].as_long()
        end = model[meeting_vars[person][1]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start//60:02}:{start%60:02}",
            "end_time": f"{end//60:02}:{end%60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No feasible schedule found")

    # Try to find a partial schedule
    partial_itinerary = []
    current_location = "Pacific Heights"
    current_time = start_time
    for person, details in people.items():
        start, end = meeting_vars[person]
        # Create a new solver for each meeting
        partial_solver = Solver()
        partial_solver.add(start >= current_time + travel_times[(current_location, details["location"])])
        partial_solver.add(end <= details["end"])
        partial_solver.add(start >= details["start"])
        partial_solver.add(end - start >= details["min_duration"])
        if partial_solver.check() == sat:
            model = partial_solver.model()
            start_time = model[start].as_long()
            end_time = model[end].as_long()
            partial_itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{start_time//60:02}:{start_time%60:02}",
                "end_time": f"{end_time//60:02}:{end_time%60:02}"
            })
            current_location = details["location"]
            current_time = end_time
    if partial_itinerary:
        print({"itinerary": partial_itinerary})
    else:
        print("No partial feasible schedule found")