from z3 import *

# Define the locations and their travel times
locations = ["Nob Hill", "Embarcadero", "The Castro", "Haight-Ashbury", "Union Square", 
             "North Beach", "Pacific Heights", "Chinatown", "Golden Gate Park", 
             "Marina District", "Russian Hill"]

travel_times = {
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Russian Hill"): 5,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Russian Hill"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Russian Hill"): 18,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Russian Hill"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Russian Hill"): 8,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Marina District"): 7,
}

# Define the people and their availability
people = {
    "Mary": {"location": "Embarcadero", "start": 2000, "end": 2115, "min_duration": 75},
    "Kenneth": {"location": "The Castro", "start": 1115, "end": 1915, "min_duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": 2000, "end": 2200, "min_duration": 120},
    "Sarah": {"location": "Union Square", "start": 1145, "end": 1430, "min_duration": 90},
    "Thomas": {"location": "North Beach", "start": 1915, "end": 1945, "min_duration": 15},
    "Daniel": {"location": "Pacific Heights", "start": 1345, "end": 2030, "min_duration": 15},
    "Richard": {"location": "Chinatown", "start": 800, "end": 1845, "min_duration": 30},
    "Mark": {"location": "Golden Gate Park", "start": 1730, "end": 2130, "min_duration": 120},
    "David": {"location": "Marina District", "start": 2000, "end": 2100, "min_duration": 60},
    "Karen": {"location": "Russian Hill", "start": 1315, "end": 1830, "min_duration": 120},
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    return time // 100 * 60 + time % 100

# Create an optimizer instance
optimizer = Optimize()

# Define variables
start_times = {person: Int(f"start_{person}") for person in people}
end_times = {person: Int(f"end_{person}") for person in people}
visited = {person: Bool(f"visited_{person}") for person in people}

# Initial location and time
initial_time = time_to_minutes(900)  # Start at 9:00 AM
current_location = "Nob Hill"

# Constraints for each person
for person, details in people.items():
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    location = details["location"]
    
    # Meeting time constraints
    optimizer.add(start_times[person] >= start)
    optimizer.add(end_times[person] <= end)
    optimizer.add(end_times[person] - start_times[person] >= min_duration)
    
    # Travel time constraints
    if person != "Richard":  # Richard is the starting point
        optimizer.add(Implies(visited[person], start_times[person] >= initial_time + travel_times[(current_location, location)]))
        optimizer.add(Implies(visited[person], end_times[person] <= end - travel_times[(location, current_location)]))
        initial_time = end_times[person]
        current_location = location

# Objective: maximize the number of meetings
objective = Sum([If(visited[person], 1, 0) for person in people])
optimizer.maximize(objective)

# Check if the problem is solvable
if optimizer.check() == sat:
    model = optimizer.model()
    itinerary = []
    for person in people.items():
        if model.evaluate(visited[person[0]]):
            start = model.evaluate(start_times[person[0]]).as_long()
            end = model.evaluate(end_times[person[0]]).as_long()
            itinerary.append({
                "action": "meet",
                "person": person[0],
                "start_time": f"{start // 60:02}:{start % 60:02}",
                "end_time": f"{end // 60:02}:{end % 60:02}"
            })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")