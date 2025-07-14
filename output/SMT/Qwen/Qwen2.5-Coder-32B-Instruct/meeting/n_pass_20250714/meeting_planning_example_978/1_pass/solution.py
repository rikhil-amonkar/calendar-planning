from z3 import *

# Define the time slots
time_slots = range(9*60, 22*60 + 1)  # From 9:00 AM to 10:00 PM in minutes

# Define the locations
locations = ["Embarcadero", "Fisherman's Wharf", "Financial District", 
             "Russian Hill", "Marina District", "Richmond District", 
             "Pacific Heights", "Haight-Ashbury", "Presidio", "Nob Hill", "The Castro"]

# Define the travel times (in minutes)
travel_times = {
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "The Castro"): 20,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "The Castro"): 22,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "The Castro"): 16,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "The Castro"): 21,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "The Castro"): 17,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Nob Hill"): 16,
}

# Define the availability of friends
friend_availability = {
    "Stephanie": ((15*60 + 30), 22*60),  # 3:30 PM to 10:00 PM
    "Lisa": ((10*60 + 45), 17*60 + 15),   # 10:45 AM to 5:15 PM
    "Melissa": ((17*60), 21*60 + 45),     # 5:00 PM to 9:45 PM
    "Betty": ((10*60 + 45), 14*15),       # 10:45 AM to 2:15 PM
    "Sarah": ((16*15 + 15), 19*60 + 30),  # 4:15 PM to 7:30 PM
    "Daniel": ((18*30 + 30), 21*60 + 45), # 6:30 PM to 9:45 PM
    "Joshua": ((9*60), 15*30),            # 9:00 AM to 3:30 PM
    "Joseph": ((7*60), 13*60),            # 7:00 AM to 1:00 PM
    "Andrew": ((19*45 + 15), 22*60),      # 7:45 PM to 10:00 PM
    "John": ((13*15 + 15), 19*45 + 30),   # 1:15 PM to 7:45 PM
}

# Define the minimum meeting times
min_meeting_times = {
    "Stephanie": 30,
    "Lisa": 15,
    "Melissa": 120,
    "Betty": 60,
    "Sarah": 105,
    "Daniel": 60,
    "Joshua": 15,
    "Joseph": 45,
    "Andrew": 105,
    "John": 45,
}

# Create the solver
solver = Solver()

# Create variables for each friend's meeting time
meeting_start = {name: Int(f"{name}_start") for name in friend_availability}
meeting_end = {name: Int(f"{name}_end") for name in friend_availability}
current_location = String("current_location")

# Add constraints for each friend's meeting
for name, (start, end) in friend_availability.items():
    solver.add(meeting_start[name] >= start)
    solver.add(meeting_end[name] <= end)
    solver.add(meeting_end[name] - meeting_start[name] >= min_meeting_times[name])

# Add constraints for traveling between locations
for i in range(len(locations)):
    for j in range(i + 1, len(locations)):
        loc1, loc2 = locations[i], locations[j]
        if (loc1, loc2) in travel_times:
            travel_time = travel_times[(loc1, loc2)]
            for name in friend_availability:
                solver.add(Implies(current_location == loc1, meeting_start[name] >= travel_time))
                solver.add(Implies(current_location == loc2, meeting_start[name] >= travel_time))

# Add initial location constraint
solver.add(current_location == "Embarcadero")

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for name in friend_availability:
        print(f"Meet {name} from {model[meeting_start[name]] / 60} to {model[meeting_end[name]] / 60}")
else:
    print("No solution found.")