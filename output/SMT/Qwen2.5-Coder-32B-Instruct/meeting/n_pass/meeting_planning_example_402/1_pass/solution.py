from z3 import *

# Define the locations and their travel times
locations = ["Golden Gate Park", "Haight-Ashbury", "Sunset District", "Marina District", "Financial District", "Union Square"]
travel_times = {
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
}

# Define the friends and their availability
friends = {
    "Sarah": {"location": "Haight-Ashbury", "start": 17*60, "end": 21*60+30, "min_duration": 105},
    "Patricia": {"location": "Sunset District", "start": 17*60, "end": 19*60+45, "min_duration": 45},
    "Matthew": {"location": "Marina District", "start": 9*60+15, "end": 12*60, "min_duration": 15},
    "Joseph": {"location": "Financial District", "start": 14*60+15, "end": 18*60+45, "min_duration": 30},
    "Robert": {"location": "Union Square", "start": 10*60+15, "end": 21*60+45, "min_duration": 15},
}

# Convert times to minutes from 00:00
start_time = 9*60  # 9:00 AM
end_time = 21*60+45  # 9:45 PM

# Create a solver
solver = Solver()

# Define variables for each friend's meeting start and end times
meeting_vars = {}
for friend, details in friends.items():
    start = Int(f"{friend}_start")
    end = Int(f"{friend}_end")
    meeting_vars[friend] = (start, end)
    solver.add(start >= details["start"])
    solver.add(end <= details["end"])
    solver.add(end - start >= details["min_duration"])

# Define variables for the current location and time
current_location = String("current_location")
current_time = Int("current_time")
solver.add(current_location == "Golden Gate Park")
solver.add(current_time == start_time)

# Define constraints for traveling between locations
for friend, (start, end) in meeting_vars.items():
    location = friends[friend]["location"]
    travel_time = travel_times[(current_location.as_string(), location)]
    solver.add(current_time + travel_time <= start)
    current_time = end
    current_location = location

# Define a function to convert minutes to HH:MM format
def minutes_to_hhmm(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend, (start, end) in meeting_vars.items():
        start_time_minutes = model[start].as_long()
        end_time_minutes = model[end].as_long()
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": minutes_to_hhmm(start_time_minutes),
            "end_time": minutes_to_hhmm(end_time_minutes)
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")