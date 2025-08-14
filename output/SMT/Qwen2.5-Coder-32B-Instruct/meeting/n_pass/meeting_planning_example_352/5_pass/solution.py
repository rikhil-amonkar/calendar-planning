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
    "Karen": {"location": "Nob Hill", "start": 2115, "end": 2145, "min_duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": 1230, "end": 1945, "min_duration": 90},
    "Sandra": {"location": "Chinatown", "start": 715, "end": 1915, "min_duration": 75},
    "Nancy": {"location": "Marina District", "start": 1100, "end": 2015, "min_duration": 105},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    return time // 100 * 60 + time % 100

# Create a solver instance
solver = Solver()

# Define variables for start and end times of meetings
meeting_start = {person: Int(f"{person}_start") for person in people}
meeting_end = {person: Int(f"{person}_end") for person in people}

# Define the start time at Union Square
start_time = time_to_minutes(900)

# Add constraints for each person
for person, details in people.items():
    loc = details["location"]
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    
    # Meeting must start after arrival and end before leaving
    solver.add(meeting_start[person] >= start_time + travel_times[("Union Square", loc)])
    solver.add(meeting_end[person] <= end)
    
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[person] - meeting_start[person] >= min_duration)
    
    # Meeting must start after the previous meeting ends and account for travel time
    for other_person in people:
        if other_person != person:
            solver.add(Or(meeting_start[person] >= meeting_end[other_person] + travel_times[(people[other_person]["location"], loc)],
                          meeting_start[other_person] >= meeting_end[person] + travel_times[(loc, people[other_person]["location"])]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start = model[meeting_start[person]].as_long()
        end = model[meeting_end[person]].as_long()
        if start < end:
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