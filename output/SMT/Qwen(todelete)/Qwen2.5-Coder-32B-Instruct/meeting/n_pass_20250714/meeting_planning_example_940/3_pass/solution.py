from z3 import *

# Define the locations
locations = [
    "Union Square", "Mission District", "Fisherman's Wharf", "Russian Hill",
    "Marina District", "North Beach", "Chinatown", "Pacific Heights",
    "The Castro", "Nob Hill", "Sunset District"
]

# Define the travel times
travel_times = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Sunset District"): 24,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Sunset District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Sunset District"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 24,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Nob Hill"): 27,
}

# Define the friends' availability
friends_availability = {
    "Kevin": ("Mission District", 2045, 2145, 60),
    "Mark": ("Fisherman's Wharf", 1715, 2000, 90),
    "Jessica": ("Russian Hill", 900, 1500, 120),
    "Jason": ("Marina District", 1515, 2145, 120),
    "John": ("North Beach", 945, 1800, 15),
    "Karen": ("Chinatown", 1645, 1900, 75),
    "Sarah": ("Pacific Heights", 1730, 1815, 45),
    "Amanda": ("The Castro", 2000, 2115, 60),
    "Nancy": ("Nob Hill", 945, 1300, 45),
    "Rebecca": ("Sunset District", 845, 1500, 75),
}

# Convert times to minutes since 9:00 AM
def convert_time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return (hours - 9) * 60 + minutes

# Create the solver
solver = Solver()

# Define variables
visited_friends = {friend: Bool(friend) for friend in friends_availability}
current_location = String('current_location')
current_time = Int('current_time')

# Initial conditions
solver.add(current_location == "Union Square")
solver.add(current_time == 0)

# Add constraints for each friend
for friend, (location, start_time, end_time, duration) in friends_availability.items():
    start_time = convert_time_to_minutes(start_time)
    end_time = convert_time_to_minutes(end_time)
    
    # Friend is visited if you are in their location during their available time
    solver.add(Implies(visited_friends[friend], And(
        current_location == location,
        current_time >= start_time,
        current_time <= end_time - duration
    )))

# Add constraints for travel times and sequence of visits
friends_list = list(friends_availability.keys())
num_friends = len(friends_list)
visit_order = [Int(f'visit_order_{i}') for i in range(num_friends)]

# Ensure each friend is visited at most once
for i in range(num_friends):
    solver.add(Or(Not(visited_friends[friends_list[i]]), visit_order[i] >= 0))
    solver.add(Or(Not(visited_friends[friends_list[i]]), visit_order[i] < num_friends))

# Ensure exactly 8 friends are visited
solver.add(Sum([If(visited_friends[friend], 1, 0) for friend in friends_availability]) == 8)

# Ensure the sequence of visits respects travel times and availability
for i in range(num_friends):
    for j in range(num_friends):
        if i != j:
            solver.add(Implies(And(visited_friends[friends_list[i]], visited_friends[friends_list[j]]), 
                               Or(visit_order[i] != visit_order[j],
                                  visit_order[i] < visit_order[j] + 1)))

# Ensure the sequence of visits respects travel times and availability
for i in range(num_friends):
    for j in range(num_friends):
        if i != j:
            friend_i = friends_list[i]
            friend_j = friends_list[j]
            solver.add(Implies(And(visited_friends[friend_i], visited_friends[friend_j], visit_order[i] < visit_order[j]), 
                               current_time + travel_times[(friends_availability[friend_i][0], 
                                                           friends_availability[friend_j][0])] 
                               <= friends_availability[friend_j][1] - friends_availability[friend_j][3]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, visited in visited_friends.items():
        if model.evaluate(visited):
            print(f"Meet {friend} at {friends_availability[friend][0]}")
else:
    print("No solution found.")