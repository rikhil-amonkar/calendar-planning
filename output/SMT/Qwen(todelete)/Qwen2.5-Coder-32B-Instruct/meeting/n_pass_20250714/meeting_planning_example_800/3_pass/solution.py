from z3 import *

# Define the locations
locations = ["Union Square", "The Castro", "North Beach", "Embarcadero", "Alamo Square", 
             "Nob Hill", "Presidio", "Fisherman's Wharf", "Mission District", "Haight-Ashbury"]

# Define the travel times in minutes
travel_times = {
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Haight-Ashbury"): 18,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Haight-Ashbury"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Haight-Ashbury"): 18,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
}

# Define the constraints
constraints = {
    "Melissa": {"location": "The Castro", "start": 8*60 + 15, "end": 9*60 + 15, "min_meeting_time": 30},
    "Kimberly": {"location": "North Beach", "start": 7*60, "end": 10*60 + 30, "min_meeting_time": 15},
    "Joseph": {"location": "Embarcadero", "start": 15*60 + 30, "end": 19*60 + 30, "min_meeting_time": 75},
    "Barbara": {"location": "Alamo Square", "start": 20*60 + 45, "end": 21*60 + 45, "min_meeting_time": 15},
    "Kenneth": {"location": "Nob Hill", "start": 12*60 + 15, "end": 17*60 + 15, "min_meeting_time": 105},
    "Joshua": {"location": "Presidio", "start": 16*60 + 30, "end": 18*60 + 15, "min_meeting_time": 105},
    "Brian": {"location": "Fisherman's Wharf", "start": 9*60 + 30, "end": 15*60 + 30, "min_meeting_time": 45},
    "Steven": {"location": "Mission District", "start": 19*60 + 30, "end": 21*60, "min_meeting_time": 90},
    "Betty": {"location": "Haight-Ashbury", "start": 19*60, "end": 20*60 + 30, "min_meeting_time": 90},
}

# Create a Z3 solver instance
solver = Solver()

# Define variables for the start time of each location visit
visit_times = {loc: Int(f"visit_{loc}") for loc in locations}

# Define binary variables to indicate whether we visit each friend's location
visit_friends = {friend: Bool(f"visit_friend_{friend}") for friend in constraints}

# Add constraints for the initial location and time
solver.add(visit_times["Union Square"] == 9*60)  # Start at Union Square at 9:00 AM

# Add constraints for meeting friends
for friend, details in constraints.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_meeting_time = details["min_meeting_time"]
    
    # If we visit the friend's location, we must meet them for the required time
    solver.add(Implies(visit_friends[friend], visit_times[loc] >= start))
    solver.add(Implies(visit_friends[friend], visit_times[loc] + min_meeting_time <= end))

# Add constraints for travel times between locations
for i in range(len(locations)):
    for j in range(i+1, len(locations)):
        loc1, loc2 = locations[i], locations[j]
        travel_time = travel_times[(loc1, loc2)]
        solver.add(visit_times[loc2] >= visit_times[loc1] + travel_time)
        solver.add(visit_times[loc1] >= visit_times[loc2] + travel_time)

# Ensure we visit exactly 7 friends
solver.add(Sum([If(visit_friends[friend], 1, 0) for friend in constraints]) == 7)

# Ensure we only visit locations where we have friends
for loc in locations:
    if loc != "Union Square":
        solver.add(Or([visit_friends[friend] for friend, details in constraints.items() if details["location"] == loc]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    schedule = [(loc, model[visit_times[loc]].as_long()) for loc in locations]
    schedule.sort(key=lambda x: x[1])
    print("SOLUTION:")
    for loc, time in schedule:
        print(f"{loc}: {time // 60}:{time % 60:02}")
else:
    print("No solution found")