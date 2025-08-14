from z3 import *

# Define the locations
locations = ["The Castro", "Marina District", "Presidio", "North Beach", "Embarcadero",
             "Haight-Ashbury", "Golden Gate Park", "Richmond District", "Alamo Square",
             "Financial District", "Sunset District"]

# Define travel times in minutes
travel_times = {
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Sunset District"): 17,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Sunset District"): 19,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Sunset District"): 15,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Sunset District"): 27,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Sunset District"): 30,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 21,
    ("Richmond District", "Sunset District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Sunset District"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
}

# Define the friends and their availability
friends = {
    "Elizabeth": {"location": "Marina District", "start": 7*60 + 0, "end": 8*60 + 45, "duration": 105},
    "Joshua": {"location": "Presidio", "start": 8*60 + 30, "end": 13*60 + 15, "duration": 105},
    "Timothy": {"location": "North Beach", "start": 19*60 + 45, "end": 22*60 + 0, "duration": 90},
    "David": {"location": "Embarcadero", "start": 10*60 + 45, "end": 12*60 + 30, "duration": 30},
    "Kimberly": {"location": "Haight-Ashbury", "start": 16*60 + 45, "end": 21*60 + 30, "duration": 75},
    "Lisa": {"location": "Golden Gate Park", "start": 17*60 + 30, "end": 21*60 + 45, "duration": 45},
    "Ronald": {"location": "Richmond District", "start": 8*60 + 0, "end": 9*60 + 30, "duration": 90},
    "Stephanie": {"location": "Alamo Square", "start": 15*60 + 30, "end": 16*60 + 30, "duration": 30},
    "Helen": {"location": "Financial District", "start": 17*60 + 30, "end": 18*60 + 30, "duration": 45},
    "Laura": {"location": "Sunset District", "start": 17*60 + 45, "end": 21*60 + 15, "duration": 90},
}

# Create a solver instance
solver = Solver()

# Define binary variables for visiting each location
visit_vars = {loc: Bool(f"visit_{loc}") for loc in locations}

# Define integer variables for the start time at each location
start_vars = {loc: Int(f"start_{loc}") for loc in locations}

# Add constraints for each friend
for friend, details in friends.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    duration = details["duration"]
    
    # We must visit the location where the friend is
    solver.add(visit_vars[loc])
    
    # We must start at the location within the friend's availability window
    solver.add(start_vars[loc] >= start)
    solver.add(start_vars[loc] <= end - duration)

# Add constraints for travel times
for i, loc1 in enumerate(locations):
    for loc2 in locations[i+1:]:
        travel_time = travel_times[(loc1, loc2)]
        
        # If we visit loc1 and loc2, we must have enough time to travel between them
        solver.add(Or(Not(visit_vars[loc1]), Not(visit_vars[loc2]),
                     start_vars[loc2] >= start_vars[loc1] + travel_time))
        solver.add(Or(Not(visit_vars[loc2]), Not(visit_vars[loc1]),
                     start_vars[loc1] >= start_vars[loc2] + travel_time))

# Start at The Castro at 9:00 AM
solver.add(start_vars["The Castro"] == 9*60)

# Ensure we visit exactly 6 friends
friend_locations = [details["location"] for details in friends.values()]
solver.add(Sum([If(visit_vars[loc], 1, 0) for loc in friend_locations]) == 6)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for loc in locations:
        if model.evaluate(visit_vars[loc]):
            start_time = model[start_vars[loc]].as_long()
            hour = start_time // 60
            minute = start_time % 60
            print(f"Visit {loc} at {hour:02}:{minute:02}")
else:
    print("No solution found")