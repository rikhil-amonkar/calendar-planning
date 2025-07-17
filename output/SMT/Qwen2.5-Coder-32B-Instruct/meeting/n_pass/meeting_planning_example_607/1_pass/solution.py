from z3 import *

# Define the locations
locations = ["Sunset District", "Russian Hill", "The Castro", "Richmond District", "Marina District", "North Beach", "Union Square", "Golden Gate Park"]

# Define the travel times
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Union Square"): 22,
}

# Define the people and their availability
people = {
    "Karen": {"location": "Russian Hill", "start": 2045, "end": 2145, "duration": 60},
    "Jessica": {"location": "The Castro", "start": 1545, "end": 1930, "duration": 60},
    "Matthew": {"location": "Richmond District", "start": 730, "end": 1515, "duration": 15},
    "Michelle": {"location": "Marina District", "start": 1030, "end": 1845, "duration": 75},
    "Carol": {"location": "North Beach", "start": 1200, "end": 1700, "duration": 90},
    "Stephanie": {"location": "Union Square", "start": 1045, "end": 1415, "duration": 30},
    "Linda": {"location": "Golden Gate Park", "start": 1045, "end": 2200, "duration": 90},
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver
solver = Solver()

# Define variables for the start time of each meeting
meeting_times = {person: Int(f"start_{person}") for person in people}

# Add constraints for each person
for person, details in people.items():
    start = meeting_times[person]
    duration = details["duration"]
    end = start + duration
    solver.add(start >= time_to_minutes(details["start"]))
    solver.add(end <= time_to_minutes(details["end"]))

# Add constraints for travel times
current_location = "Sunset District"
current_time = time_to_minutes(900)  # 9:00 AM

for person, details in people.items():
    location = details["location"]
    start = meeting_times[person]
    travel_time = travel_times[(current_location, location)]
    solver.add(start >= current_time + travel_time)
    current_time = start + details["duration"]
    current_location = location

# Add constraint for Karen's meeting
karen_start = meeting_times["Karen"]
solver.add(karen_start >= time_to_minutes(2045))
solver.add(karen_start + people["Karen"]["duration"] <= time_to_minutes(2145))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, details in people.items():
        start_time = model[meeting_times[person]].as_long()
        end_time = start_time + details["duration"]
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