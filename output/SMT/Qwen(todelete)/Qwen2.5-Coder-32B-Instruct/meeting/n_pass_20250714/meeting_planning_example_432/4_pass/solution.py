from z3 import *

# Define the locations
locations = ["Golden Gate Park", "Fisherman's Wharf", "Bayview", "Mission District", "Embarcadero", "Financial District"]

# Define the travel times in minutes
travel_times = {
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 15,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Financial District"): 19,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Financial District"): 17,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Financial District"): 5,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Embarcadero"): 4,
}

# Define the friends and their availability
friends = {
    "Joseph": {"location": "Fisherman's Wharf", "start": 8*60, "end": 17*60+30, "min_duration": 90},
    "Jeffrey": {"location": "Bayview", "start": 17*60+30, "end": 21*60+30, "min_duration": 60},
    "Kevin": {"location": "Mission District", "start": 11*60+15, "end": 15*60+15, "min_duration": 30},
    "David": {"location": "Embarcadero", "start": 8*60+15, "end": 9*60, "min_duration": 30},
    "Barbara": {"location": "Financial District", "start": 10*60+30, "end": 16*60+30, "min_duration": 15},
}

# Create a Z3 solver
solver = Solver()

# Define boolean variables indicating whether we meet each friend
meet_friend = {friend: Bool(f"meet_{friend}") for friend in friends}

# Define variables for the time spent at each location
time_spent = {friend: Int(f"time_spent_{friend}") for friend in friends}

# Define variables for the arrival time at each location
arrival_time = {location: Int(f"arrival_time_{location}") for location in locations}

# Initial arrival time at Golden Gate Park
solver.add(arrival_time["Golden Gate Park"] == 9*60)

# Constraints for meeting each friend
for friend, details in friends.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # If we decide to meet the friend, add the constraints
    solver.add(Implies(meet_friend[friend], arrival_time[loc] >= start))
    solver.add(Implies(meet_friend[friend], arrival_time[loc] + min_duration <= end))
    solver.add(Implies(meet_friend[friend], time_spent[friend] == min_duration))
    solver.add(Implies(Not(meet_friend[friend]), time_spent[friend] == 0))
    
    # Update the arrival time to account for the time spent with the friend
    next_arrival = If(meet_friend[friend], arrival_time[loc] + min_duration, arrival_time[loc])
    
    # Add constraints for traveling to the next location
    for next_loc in locations:
        if next_loc != loc:
            travel_time = travel_times[(loc, next_loc)]
            solver.add(arrival_time[next_loc] >= next_arrival + travel_time)

# Constraint to meet exactly 4 friends
solver.add(Sum([If(meet_friend[friend], 1, 0) for friend in friends]) == 4)

# Define a sequence of visits
visit_order = [Int(f"visit_order_{i}") for i in range(len(friends))]

# Ensure each visit order is unique and within the range of friends
solver.add(Distinct(visit_order))
solver.add(And([visit_order[i] >= 0 for i in range(len(friends))]))
solver.add(And([visit_order[i] < len(friends) for i in range(len(friends))]))

# Map visit order to friends
friend_list = list(friends.keys())
visit_map = {i: friend_list[i] for i in range(len(friends))}

# Add constraints for the sequence of visits
for i in range(len(friends) - 1):
    current_friend = visit_map[visit_order[i]]
    next_friend = visit_map[visit_order[i + 1]]
    current_loc = friends[current_friend]["location"]
    next_loc = friends[next_friend]["location"]
    travel_time = travel_times[(current_loc, next_loc)]
    solver.add(arrival_time[next_loc] >= arrival_time[current_loc] + time_spent[current_friend] + travel_time)

# Check if the problem is solvable
if solver.check() == sat:
    m = solver.model()
    solution = {str(d): m[d].as_long() for d in m.decls()}
    print("SOLUTION:")
    for i in range(len(friends)):
        friend_index = solution[f"visit_order_{i}"]
        friend = friend_list[friend_index]
        if solution[f"meet_{friend}"]:
            loc = friends[friend]["location"]
            start = solution[f"arrival_time_{loc}"]
            end = start + solution[f"time_spent_{friend}"]
            print(f"Meet {friend} at {loc} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
else:
    print("No solution found")