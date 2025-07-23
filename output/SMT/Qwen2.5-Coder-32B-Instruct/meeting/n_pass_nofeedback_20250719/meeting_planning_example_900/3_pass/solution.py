from z3 import *

# Define the locations and their travel times
locations = [
    "Richmond District", "The Castro", "Nob Hill", "Marina District",
    "Pacific Heights", "Haight-Ashbury", "Mission District", "Chinatown",
    "Russian Hill", "Alamo Square", "Bayview"
]

travel_times = {
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Bayview"): 19,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Bayview"): 27,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 20,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Bayview"): 16,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
}

# Define the friends and their availability
friends = {
    "Matthew": {"location": "The Castro", "start": 16.5, "end": 20.0, "min_duration": 0.75},
    "Rebecca": {"location": "Nob Hill", "start": 15.25, "end": 19.25, "min_duration": 1.75},
    "Brian": {"location": "Marina District", "start": 14.25, "end": 22.0, "min_duration": 0.5},
    "Emily": {"location": "Pacific Heights", "start": 11.25, "end": 19.75, "min_duration": 0.25},
    "Karen": {"location": "Haight-Ashbury", "start": 11.75, "end": 17.5, "min_duration": 0.5},
    "Stephanie": {"location": "Mission District", "start": 13.0, "end": 15.75, "min_duration": 1.25},
    "James": {"location": "Chinatown", "start": 14.5, "end": 19.0, "min_duration": 2.0},
    "Steven": {"location": "Russian Hill", "start": 14.0, "end": 20.0, "min_duration": 0.5},
    "Elizabeth": {"location": "Alamo Square", "start": 13.0, "end": 17.25, "min_duration": 2.0},
    "William": {"location": "Bayview", "start": 18.25, "end": 20.25, "min_duration": 1.5},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time * 60, 60)
    return int(hours) * 60 + int(minutes)

# Create a solver instance
solver = Solver()

# Define variables for each friend's meeting start time
meeting_start_times = {name: Int(f"start_{name}") for name in friends}

# Define the start time of the day in minutes (9:00 AM)
start_of_day = time_to_minutes(9.0)

# Define the end time of the day in minutes (8:00 PM)
end_of_day = time_to_minutes(20.0)

# Add constraints for each friend's meeting
for name, details in friends.items():
    start = meeting_start_times[name]
    duration = time_to_minutes(details["min_duration"])
    end = start + duration
    solver.add(start >= start_of_day)
    solver.add(end <= end_of_day)
    solver.add(start >= time_to_minutes(details["start"]))
    solver.add(end <= time_to_minutes(details["end"]))

# Add constraints for travel times between meetings
for i, (name1, details1) in enumerate(friends.items()):
    for name2, details2 in list(friends.items())[i+1:]:
        start1 = meeting_start_times[name1]
        start2 = meeting_start_times[name2]
        duration1 = time_to_minutes(details1["min_duration"])
        duration2 = time_to_minutes(details2["min_duration"])
        end1 = start1 + duration1
        end2 = start2 + duration2
        travel_time1 = travel_times[(details1["location"], details2["location"])]
        travel_time2 = travel_times[(details2["location"], details1["location"])]
        solver.add(Or(end1 + travel_time1 <= start2, end2 + travel_time2 <= start1))

# Add constraints to ensure a valid sequence of meetings
# We need to ensure that the meetings are scheduled in a way that respects travel times
# and meeting durations. We will use a list of locations to ensure a valid sequence.
location_vars = {name: Int(f"loc_{name}") for name in friends}
location_map = {loc: i for i, loc in enumerate(locations)}

# Add constraints to map each friend to a location
for name, details in friends.items():
    solver.add(location_vars[name] == location_map[details["location"]])

# Add constraints to ensure a valid sequence of meetings
for i, (name1, details1) in enumerate(friends.items()):
    for name2, details2 in list(friends.items())[i+1:]:
        start1 = meeting_start_times[name1]
        start2 = meeting_start_times[name2]
        duration1 = time_to_minutes(details1["min_duration"])
        duration2 = time_to_minutes(details2["min_duration"])
        end1 = start1 + duration1
        end2 = start2 + duration2
        travel_time1 = travel_times[(details1["location"], details2["location"])]
        travel_time2 = travel_times[(details2["location"], details1["location"])]
        solver.add(Or(end1 + travel_time1 <= start2, end2 + travel_time2 <= start1))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meetings = []
    for name, details in friends.items():
        start_time = model[meeting_start_times[name]].as_long()
        duration = time_to_minutes(details["min_duration"])
        end_time = start_time + duration
        meetings.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
            "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
        })
    meetings.sort(key=lambda x: x["start_time"])
    solution = {"itinerary": meetings}
    print(solution)
else:
    print("No solution found")