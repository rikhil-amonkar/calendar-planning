from z3 import *

# Define the locations
locations = [
    "Embarcadero", "Bayview", "Chinatown", "Alamo Square", "Nob Hill",
    "Presidio", "Union Square", "The Castro", "North Beach", "Fisherman's Wharf", "Marina District"
]

# Define the travel times between locations
travel_times = {
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Marina District"): 12,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Marina District"): 12,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Fisherman's Wharf"): 10,
}

# Define the friends' availability and meeting requirements
friends = {
    "Matthew": {"location": "Bayview", "start": 19*60 + 15, "end": 22*60, "min_meeting_time": 120},
    "Karen": {"location": "Chinatown", "start": 19*60 + 15, "end": 21*60 + 15, "min_meeting_time": 90},
    "Sarah": {"location": "Alamo Square", "start": 20*60, "end": 21*60 + 45, "min_meeting_time": 105},
    "Jessica": {"location": "Nob Hill", "start": 16*60 + 30, "end": 18*60 + 45, "min_meeting_time": 120},
    "Stephanie": {"location": "Presidio", "start": 7*60 + 30, "end": 10*60 + 15, "min_meeting_time": 60},
    "Mary": {"location": "Union Square", "start": 16*60 + 45, "end": 21*60 + 30, "min_meeting_time": 60},
    "Charles": {"location": "The Castro", "start": 16*60 + 30, "end": 22*60, "min_meeting_time": 105},
    "Nancy": {"location": "North Beach", "start": 14*60 + 45, "end": 20*60, "min_meeting_time": 15},
    "Thomas": {"location": "Fisherman's Wharf", "start": 13*60 + 30, "end": 19*60, "min_meeting_time": 30},
    "Brian": {"location": "Marina District", "start": 12*60 + 15, "end": 18*60, "min_meeting_time": 60},
}

# Create an optimizer instance
optimizer = Optimize()

# Define binary variables to indicate whether we meet each friend
meet_vars = {name: Bool(f"meet_{name}") for name in friends}

# Define variables for each friend: start_time and end_time
friend_vars = {name: (Int(f"{name}_start"), Int(f"{name}_end")) for name in friends}

# Define the current location and time
current_location = "Embarcadero"
current_time = 9 * 60  # 9:00 AM

# List to store the order of meetings
meeting_order = []

# Add constraints for each friend
for name, (start_var, end_var) in friend_vars.items():
    friend_info = friends[name]
    location = friend_info["location"]
    start = friend_info["start"]
    end = friend_info["end"]
    min_meeting_time = friend_info["min_meeting_time"]

    # Friend must be met during their availability if we choose to meet them
    optimizer.add(Implies(meet_vars[name], start_var >= start))
    optimizer.add(Implies(meet_vars[name], end_var <= end))

    # Meeting duration must be at least the minimum required if we choose to meet them
    optimizer.add(Implies(meet_vars[name], end_var - start_var >= min_meeting_time))

    # Travel time constraints if we choose to meet them
    if current_location != location:
        travel_time = travel_times[(current_location, location)]
        optimizer.add(Implies(meet_vars[name], start_var >= current_time + travel_time))
    else:
        optimizer.add(Implies(meet_vars[name], start_var >= current_time))

    # Add to meeting order
    meeting_order.append((name, start_var, end_var, location))

# Ensure we meet exactly 6 people
optimizer.add(Sum([If(meet_vars[name], 1, 0) for name in friends]) == 6)

# Ensure travel times are respected between meetings
for i in range(len(meeting_order) - 1):
    name_i, start_var_i, end_var_i, location_i = meeting_order[i]
    name_j, start_var_j, end_var_j, location_j = meeting_order[i + 1]
    travel_time = travel_times[(location_i, location_j)]
    optimizer.add(Implies(And(meet_vars[name_i], meet_vars[name_j]), start_var_j >= end_var_i + travel_time))

# Minimize the total travel time
total_travel_time = Int('total_travel_time')
optimizer.add(total_travel_time == Sum([If(meet_vars[name], travel_times[(current_location, friends[name]["location"])] if current_location != friends[name]["location"] else 0, 0) for name in friends]))
optimizer.minimize(total_travel_time)

# Check if there is a solution
if optimizer.check() == sat:
    model = optimizer.model()
    print("SOLUTION:")
    for name, (start_var, end_var) in friend_vars.items():
        if model[meet_vars[name]]:
            start_time = model[start_var].as_long()
            end_time = model[end_var].as_long()
            print(f"Meet {name} from {start_time // 60}:{start_time % 60:02d} to {end_time // 60}:{end_time % 60:02d}")
else:
    print("No solution found")