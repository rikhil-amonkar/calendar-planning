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
    "Karen": {"location": "Russian Hill", "start": 2045, "end": 2145, "min_duration": 60},
    "Jessica": {"location": "The Castro", "start": 1545, "end": 1930, "min_duration": 60},
    "Matthew": {"location": "Richmond District", "start": 730, "end": 1515, "min_duration": 15},
    "Michelle": {"location": "Marina District", "start": 1030, "end": 1845, "min_duration": 75},
    "Carol": {"location": "North Beach", "start": 1200, "end": 1700, "min_duration": 90},
    "Stephanie": {"location": "Union Square", "start": 1045, "end": 1415, "min_duration": 30},
    "Linda": {"location": "Golden Gate Park", "start": 1045, "end": 2200, "min_duration": 90},
}

# Convert times to minutes from 00:00
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver
solver = Solver()

# Define the start time for each meeting
meeting_times = {person: Int(f"start_{person}") for person in people}

# Define the location for each meeting
meeting_locations = {person: String(f"location_{person}") for person in people}

# Add constraints for each person
for person, details in people.items():
    start = meeting_times[person]
    end = start + details["min_duration"]
    solver.add(start >= time_to_minutes(details["start"]))
    solver.add(end <= time_to_minutes(details["end"]))
    solver.add(meeting_locations[person] == details["location"])

# Add constraints for travel times
for i in range(len(people) - 1):
    person1, person2 = list(people.keys())[i], list(people.keys())[i + 1]
    location1, location2 = meeting_locations[person1], meeting_locations[person2]
    start1, start2 = meeting_times[person1], meeting_times[person2]
    end1 = start1 + people[person1]["min_duration"]
    travel_time = If(location1 == location2, 0, travel_times[(location1.as_string(), location2.as_string())])
    solver.add(start2 >= end1 + travel_time)

# Add constraint for starting at Sunset District at 9:00AM
solver.add(meeting_times[list(people.keys())[0]] >= time_to_minutes(900))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start_time = model[meeting_times[person]].as_long()
        end_time = start_time + people[person]["min_duration"]
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