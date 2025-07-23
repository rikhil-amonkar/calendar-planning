from z3 import *

# Define the locations and their travel times
locations = ["Union Square", "Nob Hill", "Haight-Ashbury", "Chinatown", "Marina District"]
travel_times = {
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Marina District"): 18,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Marina District"): 11,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Nob Hill"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Chinatown"): 16,
}

# Define the people and their availability
people = {
    "Karen": {"location": "Nob Hill", "start": 2115, "end": 2145, "min_meeting": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": 1230, "end": 1945, "min_meeting": 90},
    "Sandra": {"location": "Chinatown", "start": 715, "end": 1915, "min_meeting": 75},
    "Nancy": {"location": "Marina District", "start": 1100, "end": 2015, "min_meeting": 105},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables for start and end times of meetings
meeting_start = {person: Int(f"{person}_start") for person in people}
meeting_end = {person: Int(f"{person}_end") for person in people}

# Define variables for the current location at each meeting
current_location = Int("current_location")

# Initial location is Union Square at 9:00 AM
solver.add(current_location == locations.index("Union Square"))
solver.add(meeting_start["Sandra"] == time_to_minutes(900))  # Start at Union Square at 9:00 AM

# Constraints for each person
for person, details in people.items():
    loc_index = locations.index(details["location"])
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_meeting = details["min_meeting"]
    
    # Meeting must be within the person's availability
    solver.add(meeting_start[person] >= start_time)
    solver.add(meeting_end[person] <= end_time)
    solver.add(meeting_end[person] - meeting_start[person] >= min_meeting)
    
    # Travel time constraints
    if person != "Sandra":  # Sandra is the first meeting
        prev_person = list(people.keys())[list(people.values()).index(next(item for item in people.values() if item["start"] < details["start"]))]
        prev_loc_index = locations.index(people[prev_person]["location"])
        travel_time = travel_times[(locations[prev_loc_index], locations[loc_index])]
        solver.add(meeting_start[person] >= meeting_end[prev_person] + travel_time)
        solver.add(current_location == loc_index)

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
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")