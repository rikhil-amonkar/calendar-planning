from z3 import *

# Define the locations and their travel times
locations = ["Presidio", "Haight-Ashbury", "Nob Hill", "Russian Hill", "North Beach", "Chinatown", "Union Square", "Embarcadero", "Financial District", "Marina District"]
travel_times = {
    ("Presidio", "Haight-Ashbury"): 15, ("Presidio", "Nob Hill"): 18, ("Presidio", "Russian Hill"): 14, ("Presidio", "North Beach"): 18, ("Presidio", "Chinatown"): 21, ("Presidio", "Union Square"): 22, ("Presidio", "Embarcadero"): 20, ("Presidio", "Financial District"): 23, ("Presidio", "Marina District"): 11,
    ("Haight-Ashbury", "Presidio"): 15, ("Haight-Ashbury", "Nob Hill"): 15, ("Haight-Ashbury", "Russian Hill"): 17, ("Haight-Ashbury", "North Beach"): 19, ("Haight-Ashbury", "Chinatown"): 19, ("Haight-Ashbury", "Union Square"): 19, ("Haight-Ashbury", "Embarcadero"): 20, ("Haight-Ashbury", "Financial District"): 21, ("Haight-Ashbury", "Marina District"): 17,
    ("Nob Hill", "Presidio"): 17, ("Nob Hill", "Haight-Ashbury"): 13, ("Nob Hill", "Russian Hill"): 5, ("Nob Hill", "North Beach"): 8, ("Nob Hill", "Chinatown"): 6, ("Nob Hill", "Union Square"): 7, ("Nob Hill", "Embarcadero"): 9, ("Nob Hill", "Financial District"): 9, ("Nob Hill", "Marina District"): 11,
    ("Russian Hill", "Presidio"): 14, ("Russian Hill", "Haight-Ashbury"): 17, ("Russian Hill", "Nob Hill"): 5, ("Russian Hill", "North Beach"): 5, ("Russian Hill", "Chinatown"): 9, ("Russian Hill", "Union Square"): 10, ("Russian Hill", "Embarcadero"): 8, ("Russian Hill", "Financial District"): 11, ("Russian Hill", "Marina District"): 7,
    ("North Beach", "Presidio"): 17, ("North Beach", "Haight-Ashbury"): 18, ("North Beach", "Nob Hill"): 7, ("North Beach", "Russian Hill"): 4, ("North Beach", "Chinatown"): 6, ("North Beach", "Union Square"): 7, ("North Beach", "Embarcadero"): 6, ("North Beach", "Financial District"): 8, ("North Beach", "Marina District"): 9,
    ("Chinatown", "Presidio"): 19, ("Chinatown", "Haight-Ashbury"): 19, ("Chinatown", "Nob Hill"): 9, ("Chinatown", "Russian Hill"): 7, ("Chinatown", "North Beach"): 3, ("Chinatown", "Union Square"): 7, ("Chinatown", "Embarcadero"): 5, ("Chinatown", "Financial District"): 5, ("Chinatown", "Marina District"): 12,
    ("Union Square", "Presidio"): 24, ("Union Square", "Haight-Ashbury"): 18, ("Union Square", "Nob Hill"): 9, ("Union Square", "Russian Hill"): 13, ("Union Square", "North Beach"): 10, ("Union Square", "Chinatown"): 7, ("Union Square", "Embarcadero"): 11, ("Union Square", "Financial District"): 9, ("Union Square", "Marina District"): 18,
    ("Embarcadero", "Presidio"): 20, ("Embarcadero", "Haight-Ashbury"): 21, ("Embarcadero", "Nob Hill"): 10, ("Embarcadero", "Russian Hill"): 8, ("Embarcadero", "North Beach"): 5, ("Embarcadero", "Chinatown"): 7, ("Embarcadero", "Union Square"): 10, ("Embarcadero", "Financial District"): 5, ("Embarcadero", "Marina District"): 12,
    ("Financial District", "Presidio"): 22, ("Financial District", "Haight-Ashbury"): 19, ("Financial District", "Nob Hill"): 8, ("Financial District", "Russian Hill"): 11, ("Financial District", "North Beach"): 7, ("Financial District", "Chinatown"): 5, ("Financial District", "Union Square"): 9, ("Financial District", "Embarcadero"): 4, ("Financial District", "Marina District"): 15,
    ("Marina District", "Presidio"): 10, ("Marina District", "Haight-Ashbury"): 16, ("Marina District", "Nob Hill"): 12, ("Marina District", "Russian Hill"): 8, ("Marina District", "North Beach"): 11, ("Marina District", "Chinatown"): 15, ("Marina District", "Union Square"): 16, ("Marina District", "Embarcadero"): 14, ("Marina District", "Financial District"): 17,
}

# Define the people and their availability
people = {
    "Karen": {"location": "Haight-Ashbury", "start": 2100, "end": 2145, "min_duration": 45},
    "Jessica": {"location": "Nob Hill", "start": 1345, "end": 2100, "min_duration": 90},
    "Brian": {"location": "Russian Hill", "start": 1530, "end": 2145, "min_duration": 60},
    "Kenneth": {"location": "North Beach", "start": 945, "end": 2100, "min_duration": 30},
    "Jason": {"location": "Chinatown", "start": 815, "end": 1145, "min_duration": 75},
    "Stephanie": {"location": "Union Square", "start": 1445, "end": 1845, "min_duration": 105},
    "Kimberly": {"location": "Embarcadero", "start": 945, "end": 1930, "min_duration": 75},
    "Steven": {"location": "Financial District", "start": 715, "end": 2115, "min_duration": 60},
    "Mark": {"location": "Marina District", "start": 1015, "end": 1300, "min_duration": 75},
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    return time // 100 * 60 + time % 100

# Create a solver instance
solver = Solver()

# Define variables
start_times = {person: Int(f"start_{person}") for person in people}
end_times = {person: Int(f"end_{person}") for person in people}
current_location = String("current_location")
next_location = String("next_location")
travel_time = Int("travel_time")

# Initial location and time
solver.add(current_location == "Presidio")
solver.add(start_times["Jason"] == time_to_minutes(people["Jason"]["start"]))

# Constraints for each person
for person, details in people.items():
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    location = details["location"]
    
    # Meeting time constraints
    solver.add(start_times[person] >= start)
    solver.add(end_times[person] <= end)
    solver.add(end_times[person] - start_times[person] >= min_duration)
    
    # Travel time constraints
    if person != "Jason":  # Jason is the first meeting
        solver.add(start_times[person] >= end_times[last_person] + travel_times[(last_location, location)])
    
    last_person = person
    last_location = location

# Objective: Maximize the number of meetings
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(Sum([If(start_times[person] < end_times[person], 1, 0) for person in people]))

# Solve the problem
if objective.check() == sat:
    model = objective.model()
    itinerary = []
    for person in people:
        start = model.evaluate(start_times[person]).as_long()
        end = model.evaluate(end_times[person]).as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")