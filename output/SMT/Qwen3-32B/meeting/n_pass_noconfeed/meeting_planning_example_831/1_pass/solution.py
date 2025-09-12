from z3 import *
import json

friends = [
    {
        'name': 'Jeffrey',
        'location': 1,  # Fisherman's Wharf
        'available_start': 615,
        'available_end': 780,
        'min_duration': 90
    },
    {
        'name': 'Ronald',
        'location': 2,  # Alamo Square
        'available_start': 465,
        'available_end': 885,
        'min_duration': 120
    },
    {
        'name': 'Jason',
        'location': 3,  # Financial District
        'available_start': 645,
        'available_end': 960,
        'min_duration': 105
    },
    {
        'name': 'Melissa',
        'location': 4,  # Union Square
        'available_start': 1065,
        'available_end': 1095,
        'min_duration': 15
    },
    {
        'name': 'Elizabeth',
        'location': 5,  # Sunset District
        'available_start': 885,
        'available_end': 1050,
        'min_duration': 105
    },
    {
        'name': 'Margaret',
        'location': 6,  # Embarcadero
        'available_start': 795,
        'available_end': 1140,
        'min_duration': 90
    },
    {
        'name': 'George',
        'location': 7,  # Golden Gate Park
        'available_start': 1140,
        'available_end': 1320,
        'min_duration': 75
    },
    {
        'name': 'Richard',
        'location': 8,  # Chinatown
        'available_start': 570,
        'available_end': 1260,
        'min_duration': 15
    },
    {
        'name': 'Laura',
        'location': 9,  # Richmond District
        'available_start': 585,
        'available_end': 1080,
        'min_duration': 60
    }
]

travel_times = [
    # Presidio, Fisherman's Wharf, Alamo Square, Financial District, Union Square, Sunset District, Embarcadero, Golden Gate Park, Chinatown, Richmond District
    [0, 19, 19, 23, 22, 15, 20, 12, 21, 7],  # Presidio
    [17, 0, 21, 11, 13, 27, 8, 25, 12, 18],  # Fisherman's Wharf
    [17, 21, 0, 17, 14, 16, 16, 9, 15, 11],  # Alamo Square
    [22, 10, 17, 0, 9, 30, 4, 23, 5, 21],  # Financial District
    [24, 15, 15, 9, 0, 27, 11, 22, 7, 20],  # Union Square
    [16, 29, 17, 30, 30, 0, 30, 11, 30, 12],  # Sunset District
    [20, 6, 19, 5, 10, 30, 0, 25, 7, 21],  # Embarcadero
    [11, 24, 9, 26, 22, 10, 25, 0, 23, 9],  # Golden Gate Park
    [19, 8, 17, 5, 7, 29, 5, 23, 0, 20],  # Chinatown
    [7, 18, 13, 22, 21, 11, 19, 9, 20, 0],  # Richmond District
]

friends_count = len(friends)
steps = friends_count  # maximum possible steps

solver = Optimize()

# Define variables
friend_idx = [Int(f"friend_idx_{i}") for i in range(steps)]
start_time = [Int(f"start_time_{i}") for i in range(steps)]
end_time = [Int(f"end_time_{i}") for i in range(steps)]

locations = [
    "Presidio",
    "Fisherman's Wharf",
    "Alamo Square",
    "Financial District",
    "Union Square",
    "Sunset District",
    "Embarcadero",
    "Golden Gate Park",
    "Chinatown",
    "Richmond District"
]

# Helper functions to get friend's properties based on friend index
def get_location(friend_idx_var):
    loc = 0
    for i in range(friends_count):
        loc = If(friend_idx_var == i, friends[i]['location'], loc)
    return loc

def get_available_start(friend_idx_var):
    start = 0
    for i in range(friends_count):
        start = If(friend_idx_var == i, friends[i]['available_start'], start)
    return start

def get_available_end(friend_idx_var):
    end = 0
    for i in range(friends_count):
        end = If(friend_idx_var == i, friends[i]['available_end'], end)
    return end

def get_min_duration(friend_idx_var):
    duration = 0
    for i in range(friends_count):
        duration = If(friend_idx_var == i, friends[i]['min_duration'], duration)
    return duration

# Helper function to get travel time between two location codes
def get_travel_time(prev_loc, curr_loc):
    tt = 0
    for i in range(10):
        for j in range(10):
            tt = If(And(prev_loc == i, curr_loc == j), travel_times[i][j], tt)
    return tt

# Add constraints for each step
# Step 0
solver.add(Implies(friend_idx[0] != -1, start_time[0] >= 540 + get_travel_time(0, get_location(friend_idx[0]))))
solver.add(Implies(friend_idx[0] != -1, start_time[0] >= get_available_start(friend_idx[0])))
solver.add(Implies(friend_idx[0] != -1, end_time[0] == start_time[0] + get_min_duration(friend_idx[0])))
solver.add(Implies(friend_idx[0] != -1, end_time[0] <= get_available_end(friend_idx[0])))

# Steps 1 to steps-1
for i in range(1, steps):
    # If current friend is not -1, then previous is not -1
    solver.add(Implies(friend_idx[i] != -1, friend_idx[i-1] != -1))
    
    prev_loc = get_location(friend_idx[i-1])
    curr_loc = get_location(friend_idx[i])
    travel_time = get_travel_time(prev_loc, curr_loc)
    
    solver.add(Implies(friend_idx[i] != -1, start_time[i] >= end_time[i-1] + travel_time))
    solver.add(Implies(friend_idx[i] != -1, start_time[i] >= get_available_start(friend_idx[i])))
    solver.add(Implies(friend_idx[i] != -1, end_time[i] == start_time[i] + get_min_duration(friend_idx[i])))
    solver.add(Implies(friend_idx[i] != -1, end_time[i] <= get_available_end(friend_idx[i])))

# Add constraints for friend indices to be in range
for i in range(steps):
    solver.add(And(friend_idx[i] >= -1, friend_idx[i] <= friends_count - 1))

# Add uniqueness constraints
for i in range(steps):
    for j in range(i+1, steps):
        solver.add(Or(friend_idx[i] == -1, friend_idx[j] == -1, friend_idx[i] != friend_idx[j]))

# Maximize the number of friends met
total_met = Sum([If(friend_idx[i] != -1, 1, 0) for i in range(steps)])
solver.maximize(total_met)

# Check for solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(steps):
        fi_val = model[friend_idx[i]].as_long()
        if fi_val != -1:
            fi = fi_val
            name = friends[fi]['name']
            loc_code = friends[fi]['location']
            loc_name = locations[loc_code]
            st = model[start_time[i]].as_long()
            et = model[end_time[i]].as_long()
            # Format time as H:MM
            def format_time(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            itinerary.append({
                "action": "meet",
                "location": loc_name,
                "person": name,
                "start_time": format_time(st),
                "end_time": format_time(et)
            })
    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")