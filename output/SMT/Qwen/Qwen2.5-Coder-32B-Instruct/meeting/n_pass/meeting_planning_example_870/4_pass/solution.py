from z3 import *

# Define the locations
locations = [
    "Pacific Heights", "Marina District", "The Castro", "Richmond District",
    "Alamo Square", "Financial District", "Presidio", "Mission District",
    "Nob Hill", "Russian Hill"
]

# Define the travel times as a dictionary
travel_times = {
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 11,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Russian Hill"): 13,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Russian Hill"): 15,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Nob Hill"): 5,
}

# Define the friends' availability
availability = {
    "Linda": ("Marina District", 18, 22),  # 6:00PM to 10:00PM
    "Kenneth": ("The Castro", 14.75, 16.25),  # 2:45PM to 4:15PM
    "Kimberly": ("Richmond District", 14.25, 22),  # 2:15PM to 10:00PM
    "Paul": ("Alamo Square", 21.5, 21.5),  # 9:00PM to 9:30PM
    "Carol": ("Financial District", 10.25, 12),  # 10:15AM to 12:00PM
    "Brian": ("Presidio", 10, 21.5),  # 10:00AM to 9:30PM
    "Laura": ("Mission District", 16.25, 20.5),  # 4:15PM to 8:30PM
    "Sandra": ("Nob Hill", 9.25, 18.5),  # 9:15AM to 6:30PM
    "Karen": ("Russian Hill", 18.5, 22)  # 6:30PM to 10:00PM
}

# Define the minimum meeting times
min_meeting_times = {
    "Linda": 0.5,  # 30 minutes
    "Kenneth": 0.5,  # 30 minutes
    "Kimberly": 0.5,  # 30 minutes
    "Paul": 0.25,  # 15 minutes
    "Carol": 1,  # 60 minutes
    "Brian": 1.25,  # 75 minutes
    "Laura": 0.5,  # 30 minutes
    "Sandra": 1,  # 60 minutes
    "Karen": 1.25  # 75 minutes
}

# Function to check if a schedule is valid
def check_schedule(num_friends):
    solver = Solver()
    
    # Define the variables
    arrival_times = {loc: Real(f"arrival_{loc}") for loc in locations}
    visited_friends = {name: Bool(f"visited_{name}") for name in availability.keys()}
    
    # Add constraints for arrival times
    solver.add(arrival_times["Pacific Heights"] == 9)
    
    # Add constraints for each friend
    for name, (loc, start, end) in availability.items():
        solver.add(visited_friends[name] == And(
            arrival_times[loc] <= end - min_meeting_times[name],
            arrival_times[loc] + min_meeting_times[name] >= start
        ))
    
    # Add constraints for travel times
    for i in range(len(locations)):
        for j in range(len(locations)):
            if i != j:
                loc1, loc2 = locations[i], locations[j]
                solver.add(arrival_times[loc2] >= arrival_times[loc1] + travel_times[(loc1, loc2)] / 60.0)
    
    # Add constraint to visit exactly num_friends friends
    solver.add(Sum([If(visited_friends[name], 1, 0) for name in visited_friends.keys()]) == num_friends)
    
    # Check if the problem is solvable
    if solver.check() == sat:
        return solver.model(), True
    else:
        return None, False

# Find the optimal schedule
model, is_valid = check_schedule(9)
if is_valid:
    print("SOLUTION:")
    for name in visited_friends.keys():
        if model.evaluate(visited_friends[name]):
            loc, start, end = availability[name]
            meeting_start = model.evaluate(arrival_times[loc]).as_decimal(2)
            meeting_end = meeting_start + min_meeting_times[name]
            print(f"Meet {name} at {loc} from {meeting_start} to {meeting_end}")
else:
    print("No solution found")