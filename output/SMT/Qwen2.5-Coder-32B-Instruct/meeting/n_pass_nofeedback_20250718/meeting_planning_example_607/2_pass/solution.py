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

# Define variables for start and end times of each meeting
meeting_times = {}
for person, details in people.items():
    start = Int(f"{person}_start")
    end = Int(f"{person}_end")
    meeting_times[person] = (start, end)
    solver.add(start >= time_to_minutes(details["start"]))
    solver.add(end <= time_to_minutes(details["end"]))
    solver.add(end - start >= details["min_duration"])

# Define a variable for the current time
current_time = Int("current_time")
solver.add(current_time == time_to_minutes(900))  # Start at 9:00 AM

# Define a list to keep track of the sequence of meetings
meetings = list(people.keys())
meetings.sort(key=lambda x: time_to_minutes(people[x]["start"]))  # Sort by start time

# Add constraints for each meeting
for i in range(len(meetings)):
    person = meetings[i]
    start, end = meeting_times[person]
    if i == 0:
        # First meeting
        solver.add(current_time + travel_times[("Sunset District", people[person]["location"])] <= start)
    else:
        # Subsequent meetings
        prev_person = meetings[i - 1]
        prev_end = meeting_times[prev_person][1]
        solver.add(prev_end + travel_times[(people[prev_person]["location"], people[person]["location"])] <= start)
    current_time = end

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, details in people.items():
        start = model[meeting_times[person][0]].as_long()
        end = model[meeting_times[person][1]].as_long()
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