from z3 import *

# Define the locations and their travel times
locations = ["Financial District", "Golden Gate Park", "Chinatown", "Union Square", "Fisherman's Wharf", "Pacific Heights", "North Beach"]
location_indices = {loc: i for i, loc in enumerate(locations)}
travel_times = {
    (0, 1): 23,  # Financial District to Golden Gate Park
    (0, 2): 5,   # Financial District to Chinatown
    (0, 3): 9,   # Financial District to Union Square
    (0, 4): 10,  # Financial District to Fisherman's Wharf
    (0, 5): 13,  # Financial District to Pacific Heights
    (0, 6): 7,   # Financial District to North Beach
    (1, 0): 26,  # Golden Gate Park to Financial District
    (1, 2): 23,  # Golden Gate Park to Chinatown
    (1, 3): 22,  # Golden Gate Park to Union Square
    (1, 4): 24,  # Golden Gate Park to Fisherman's Wharf
    (1, 5): 16,  # Golden Gate Park to Pacific Heights
    (1, 6): 24,  # Golden Gate Park to North Beach
    (2, 0): 5,   # Chinatown to Financial District
    (2, 1): 23,  # Chinatown to Golden Gate Park
    (2, 3): 7,   # Chinatown to Union Square
    (2, 4): 8,   # Chinatown to Fisherman's Wharf
    (2, 5): 10,  # Chinatown to Pacific Heights
    (2, 6): 3,   # Chinatown to North Beach
    (3, 0): 9,   # Union Square to Financial District
    (3, 1): 22,  # Union Square to Golden Gate Park
    (3, 2): 7,   # Union Square to Chinatown
    (3, 4): 15,  # Union Square to Fisherman's Wharf
    (3, 5): 15,  # Union Square to Pacific Heights
    (3, 6): 10,  # Union Square to North Beach
    (4, 0): 11,  # Fisherman's Wharf to Financial District
    (4, 1): 25,  # Fisherman's Wharf to Golden Gate Park
    (4, 2): 12,  # Fisherman's Wharf to Chinatown
    (4, 3): 13,  # Fisherman's Wharf to Union Square
    (4, 5): 12,  # Fisherman's Wharf to Pacific Heights
    (4, 6): 6,   # Fisherman's Wharf to North Beach
    (5, 0): 13,  # Pacific Heights to Financial District
    (5, 1): 15,  # Pacific Heights to Golden Gate Park
    (5, 2): 11,  # Pacific Heights to Chinatown
    (5, 3): 12,  # Pacific Heights to Union Square
    (5, 4): 13,  # Pacific Heights to Fisherman's Wharf
    (5, 6): 9,   # Pacific Heights to North Beach
    (6, 0): 8,   # North Beach to Financial District
    (6, 1): 22,  # North Beach to Golden Gate Park
    (6, 2): 6,   # North Beach to Chinatown
    (6, 3): 7,   # North Beach to Union Square
    (6, 4): 5,   # North Beach to Fisherman's Wharf
    (6, 5): 8,   # North Beach to Pacific Heights
}

# Define the meetings and their constraints
meetings = {
    "Stephanie": {"location": "Golden Gate Park", "start": 660, "end": 1800, "min_duration": 105},
    "Karen": {"location": "Chinatown", "start": 945, "end": 2610, "min_duration": 15},
    "Brian": {"location": "Union Square", "start": 1800, "end": 3090, "min_duration": 30},
    "Rebecca": {"location": "Fisherman's Wharf", "start": 480, "end": 675, "min_duration": 30},
    "Joseph": {"location": "Pacific Heights", "start": 510, "end": 570, "min_duration": 60},
    "Steven": {"location": "North Beach", "start": 1530, "end": 5070, "min_duration": 120},
}

# Convert times to minutes from 00:00
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_vars = {}
for person, details in meetings.items():
    start = Int(f"{person}_start")
    end = Int(f"{person}_end")
    meeting_vars[person] = (start, end)
    solver.add(start >= details["start"])
    solver.add(end <= details["end"])
    solver.add(end - start >= details["min_duration"])

# Define a list to store the sequence of locations and times
location_vars = [Int(f"location_{i}") for i in range(len(meetings) + 1)]
time_vars = [Int(f"time_{i}") for i in range(len(meetings) + 1)]

# Initial location and time
solver.add(location_vars[0] == location_indices["Financial District"])
solver.add(time_vars[0] == time_to_minutes("09:00"))

# Add constraints for each meeting
for i, person in enumerate(meetings.keys()):
    start, end = meeting_vars[person]
    details = meetings[person]
    location = location_indices[details["location"]]
    # Travel time to the meeting location
    travel_time = Int(f"travel_time_{i}")
    solver.add(travel_time == travel_times[(location_vars[i], location)])
    solver.add(start >= time_vars[i] + travel_time)
    # Update current location and time after the meeting
    solver.add(location_vars[i + 1] == location)
    solver.add(time_vars[i + 1] == end)

# Define the objective: maximize the number of meetings
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(Sum([If(start != end, 1, 0) for start, end in meeting_vars.values()]))

# Check if the problem is solvable
if objective.check() == sat:
    model = objective.model()
    itinerary = []
    for person, (start, end) in meeting_vars.items():
        start_time = model.evaluate(start).as_long()
        end_time = model.evaluate(end).as_long()
        if start_time != end_time:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
                "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
            })
    print({"itinerary": itinerary})
else:
    print("No solution found")