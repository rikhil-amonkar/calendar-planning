from z3 import *

# Define the friends and their availability
friends = {
    "William": (3*60 + 15, 5*60 + 15, 60),
    "Joshua": (7*60, 20*60, 15),
    "Joseph": (11*60 + 15, 1*60 + 30, 15),
    "David": (4*60 + 45, 7*60 + 15, 45),
    "Brian": (1*60 + 45, 8*60 + 45, 105),
    "Karen": (11*60 + 30, 18*60 + 30, 15),
    "Anthony": (7*60 + 15, 10*60 + 30, 30),
    "Matthew": (5*60 + 15, 7*60 + 15, 120),
    "Helen": (8*60, 12*60, 75),
    "Jeffrey": (19*60, 21*60 + 30, 60)
}

# Define the travel times (in minutes)
travel_times = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 11,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 12,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 16,
    ("Golden Gate Park", "The Castro"): 11,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Pacific Heights"): 16,
}

# Create the solver
solver = Solver()

# Define variables
start_times = {name: Int(f"start_{name}") for name in friends}
locations = {name: String(f"location_{name}") for name in friends}

# Add constraints
for name, (start, end, duration) in friends.items():
    solver.add(start_times[name] >= start)
    solver.add(start_times[name] + duration <= end)

# Initial location is The Castro at 9:00 AM
initial_location = "The Castro"
current_time = 9 * 60

# Ensure the order of visits respects travel times and meeting times
friends_list = list(friends.keys())
for i in range(len(friends_list)):
    if i == 0:
        solver.add(locations[friends_list[i]] == initial_location)
        solver.add(start_times[friends_list[i]] >= current_time)
    else:
        prev_friend = friends_list[i-1]
        current_friend = friends_list[i]
        solver.add(start_times[current_friend] >= start_times[prev_friend] + friends[prev_friend][2] + travel_times[(locations[prev_friend], locations[current_friend])])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    schedule = []
    for name in friends_list:
        start_time = model[start_times[name]].as_long()
        location = model[locations[name]].as_string()
        schedule.append((name, start_time, start_time + friends[name][2], location))
    
    # Sort the schedule by start time
    schedule.sort(key=lambda x: x[1])
    
    print("SOLUTION:")
    for name, start, end, location in schedule:
        print(f"{name}: {start//60}:{start%60:02d} - {end//60}:{end%60:02d} at {location}")
else:
    print("No solution found.")