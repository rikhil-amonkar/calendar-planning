from z3 import *

# Define the locations and their travel times
locations = ["The Castro", "North Beach", "Golden Gate Park", "Embarcadero", "Haight-Ashbury", 
             "Richmond District", "Nob Hill", "Marina District", "Presidio", "Union Square", "Financial District"]

travel_times = {
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Financial District"): 21,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Financial District"): 8,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Financial District"): 26,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Financial District"): 17,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Financial District"): 23,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Financial District"): 9,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9,
}

# Define the meetings and their constraints
meetings = {
    "Steven": {"location": "North Beach", "start": 17.5, "end": 20.5, "min_duration": 0.25},
    "Sarah": {"location": "Golden Gate Park", "start": 17.0, "end": 19.25, "min_duration": 1.25},
    "Brian": {"location": "Embarcadero", "start": 14.25, "end": 16.0, "min_duration": 1.75},
    "Stephanie": {"location": "Haight-Ashbury", "start": 10.25, "end": 12.25, "min_duration": 1.25},
    "Melissa": {"location": "Richmond District", "start": 14.0, "end": 19.5, "min_duration": 0.5},
    "Nancy": {"location": "Nob Hill", "start": 8.25, "end": 12.75, "min_duration": 1.5},
    "David": {"location": "Marina District", "start": 11.25, "end": 13.25, "min_duration": 2.0},
    "James": {"location": "Presidio", "start": 15.0, "end": 18.25, "min_duration": 2.0},
    "Elizabeth": {"location": "Union Square", "start": 11.5, "end": 21.0, "min_duration": 1.0},
    "Robert": {"location": "Financial District", "start": 13.25, "end": 15.25, "min_duration": 0.75},
}

# Create a solver instance
solver = Solver()

# Define the number of meetings
num_meetings = len(meetings)

# Define the variables for the sequence of meetings
meeting_vars = [Int(f'meeting_{i}') for i in range(num_meetings)]
location_vars = [String(f'location_{i}') for i in range(num_meetings)]
start_times = [Real(f'start_time_{i}') for i in range(num_meetings)]
end_times = [Real(f'end_time_{i}') for i in range(num_meetings)]

# Map meeting names to indices
meeting_indices = {name: i for i, name in enumerate(meetings)}

# Initial conditions
solver.add(location_vars[0] == "The Castro")
solver.add(start_times[0] == 9.0)

# Define the constraints for each meeting
for i, name in enumerate(meetings):
    details = meetings[name]
    location = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # Constraints for meeting
    solver.add(start_times[i] >= start)
    solver.add(end_times[i] <= end)
    solver.add(end_times[i] - start_times[i] >= min_duration)
    
    # Constraints for travel and meeting
    if i > 0:
        prev_location = location_vars[i-1]
        travel_time = travel_times[(prev_location, location)]
        solver.add(start_times[i] >= end_times[i-1] + travel_time / 60.0)
    
    solver.add(location_vars[i] == location)

# Maximize the number of meetings
solver.maximize(Sum([If(meeting_vars[i] == meeting_indices[name], 1, 0) for i, name in enumerate(meetings)]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i, name in enumerate(meetings):
        if model.evaluate(meeting_vars[i]) == meeting_indices[name]:
            start = model.evaluate(start_times[i]).as_decimal(2)
            end = model.evaluate(end_times[i]).as_decimal(2)
            itinerary.append({"action": "meet", "person": name, "start_time": f"{int(start):02}:{int((start % 1) * 60):02}", "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")