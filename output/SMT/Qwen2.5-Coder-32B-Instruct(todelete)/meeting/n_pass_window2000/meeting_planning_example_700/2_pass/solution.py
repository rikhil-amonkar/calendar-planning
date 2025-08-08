from z3 import *

# Define the locations and their travel times
locations = ["Presidio", "Pacific Heights", "Golden Gate Park", "Fisherman's Wharf", 
             "Marina District", "Alamo Square", "Sunset District", "Nob Hill", "North Beach"]

travel_times = {
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "North Beach"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "North Beach"): 23,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "North Beach"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Nob Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "North Beach"): 8,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Nob Hill"): 7,
}

# Define the meetings and their constraints
meetings = {
    "Kevin": {"location": "Pacific Heights", "start": 7.25, "end": 8.75, "duration": 1.5},
    "Michelle": {"location": "Golden Gate Park", "start": 20.0, "end": 21.0, "duration": 0.25},
    "Emily": {"location": "Fisherman's Wharf", "start": 16.25, "end": 19.0, "duration": 0.5},
    "Mark": {"location": "Marina District", "start": 18.25, "end": 19.75, "duration": 1.25},
    "Barbara": {"location": "Alamo Square", "start": 17.0, "end": 19.0, "duration": 2.0},
    "Laura": {"location": "Sunset District", "start": 19.0, "end": 21.25, "duration": 1.25},
    "Mary": {"location": "Nob Hill", "start": 17.5, "end": 19.0, "duration": 0.75},
    "Helen": {"location": "North Beach", "start": 11.0, "end": 12.25, "duration": 0.75},
}

# Convert travel times to minutes
travel_times_minutes = {(a, b): t * 60 for (a, b), t in travel_times.items()}

# Convert meeting times to minutes
meetings_minutes = {name: {"location": details["location"], 
                           "start": details["start"] * 60, 
                           "end": details["end"] * 60, 
                           "duration": details["duration"] * 60} 
                    for name, details in meetings.items()}

# Create a solver
solver = Solver()

# Define variables
num_steps = len(meetings) + 1  # One step for each meeting plus the initial step
current_location = [String(f'current_location_{i}') for i in range(num_steps)]
current_time = [Real(f'current_time_{i}') for i in range(num_steps)]
meetings_vars = {name: Bool(name) for name in meetings}

# Initial conditions
solver.add(current_location[0] == "Presidio")
solver.add(current_time[0] == 9 * 60)  # 9:00 AM in minutes

# Define constraints for each meeting
for i, name in enumerate(meetings):
    details = meetings_minutes[name]
    location = details["location"]
    start = details["start"]
    end = details["end"]
    duration = details["duration"]

    # Define the meeting variables
    meet_var = meetings_vars[name]

    # Constraints for meeting
    solver.add(Implies(meet_var, current_location[i + 1] == location))
    solver.add(Implies(meet_var, current_time[i] + travel_times_minutes[(current_location[i], location)] >= start))
    solver.add(Implies(meet_var, current_time[i] + travel_times_minutes[(current_location[i], location)] + duration <= end))