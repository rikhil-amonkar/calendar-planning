from z3 import *

# Define the locations and their travel times
locations = [
    "Union Square", "Mission District", "Fisherman's Wharf", "Russian Hill",
    "Marina District", "North Beach", "Chinatown", "Pacific Heights",
    "The Castro", "Nob Hill", "Sunset District"
]

travel_times = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    # Add all other travel times similarly
}

# Reverse travel times
for (start, end) in list(travel_times.keys()):
    travel_times[(end, start)] = travel_times[(start, end)]

# Define the people and their availability
people = {
    "Kevin": {"location": "Mission District", "start": 2045, "end": 2145, "duration": 60},
    "Mark": {"location": "Fisherman's Wharf", "start": 1715, "end": 2000, "duration": 90},
    "Jessica": {"location": "Russian Hill", "start": 900, "end": 1500, "duration": 120},
    "Jason": {"location": "Marina District", "start": 1515, "end": 2145, "duration": 120},
    "John": {"location": "North Beach", "start": 945, "end": 1800, "duration": 15},
    "Karen": {"location": "Chinatown", "start": 1645, "end": 1900, "duration": 75},
    "Sarah": {"location": "Pacific Heights", "start": 1730, "end": 1815, "duration": 45},
    "Amanda": {"location": "The Castro", "start": 2000, "end": 2115, "duration": 60},
    "Nancy": {"location": "Nob Hill", "start": 945, "end": 1300, "duration": 45},
    "Rebecca": {"location": "Sunset District", "start": 845, "end": 1500, "duration": 75},
}

# Convert times to minutes since 00:00
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a Z3 solver
solver = Solver()

# Define variables for meeting times
meet_vars = {}
for person, details in people.items():
    start = Int(f"{person}_start")
    end = Int(f"{person}_end")
    meet_vars[person] = (start, end)
    solver.add(start >= time_to_minutes(details["start"]))
    solver.add(end <= time_to_minutes(details["end"]))
    solver.add(end - start >= details["duration"])

# Define variables for location changes
location_vars = {}
for i in range(len(people) + 1):
    location_vars[i] = String(f"location_{i}")

# Initial location is Union Square at 9:00 AM
solver.add(location_vars[0] == "Union Square")

# Add constraints for travel times and meeting locations
for i, (person, details) in enumerate(people.items()):
    start, end = meet_vars[person]
    solver.add(location_vars[i + 1] == details["location"])
    if i > 0:
        prev_person = list(people.keys())[i - 1]
        prev_end = meet_vars[prev_person][1]
        travel_time = travel_times[(location_vars[i].as_string(), details["location"])]
        solver.add(start >= prev_end + travel_time)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    current_location = "Union Square"
    current_time = 9 * 60  # 9:00 AM in minutes

    for i, (person, details) in enumerate(people.items()):
        start = model[meet_vars[person][0]].as_long()
        end = model[meet_vars[person][1]].as_long()
        travel_time = travel_times[(current_location, details["location"])]
        current_time += travel_time
        itinerary.append({
            "action": "travel",
            "from": current_location,
            "to": details["location"],
            "start_time": f"{current_time // 60:02}:{current_time % 60:02}",
            "end_time": f"{start // 60:02}:{start % 60:02}"
        })
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
        current_location = details["location"]
        current_time = end

    print({"itinerary": itinerary})
else:
    print("No solution found")