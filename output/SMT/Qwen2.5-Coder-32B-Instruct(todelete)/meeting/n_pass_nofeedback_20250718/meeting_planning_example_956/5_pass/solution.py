from z3 import *
import json

# Define the locations and their travel times
locations = ["The Castro", "Alamo Square", "Richmond District", "Financial District", 
             "Union Square", "Fisherman's Wharf", "Marina District", "Haight-Ashbury", 
             "Mission District", "Pacific Heights", "Golden Gate Park"]

location_indices = {loc: i for i, loc in enumerate(locations)}

travel_times = {
    (0, 1): 8,
    (0, 2): 16,
    (0, 3): 21,
    (0, 4): 19,
    (0, 5): 24,
    (0, 6): 21,
    (0, 7): 6,
    (0, 8): 7,
    (0, 9): 16,
    (0, 10): 11,
    (1, 0): 8,
    (1, 2): 11,
    (1, 3): 17,
    (1, 4): 14,
    (1, 5): 19,
    (1, 6): 15,
    (1, 7): 5,
    (1, 8): 10,
    (1, 9): 10,
    (1, 10): 9,
    (2, 0): 16,
    (2, 1): 11,
    (2, 3): 22,
    (2, 4): 21,
    (2, 5): 18,
    (2, 6): 9,
    (2, 7): 10,
    (2, 8): 20,
    (2, 9): 10,
    (2, 10): 9,
    (3, 0): 20,
    (3, 1): 17,
    (3, 2): 21,
    (3, 4): 9,
    (3, 5): 10,
    (3, 6): 15,
    (3, 7): 19,
    (3, 8): 17,
    (3, 9): 13,
    (3, 10): 23,
    (4, 0): 17,
    (4, 1): 15,
    (4, 2): 20,
    (4, 3): 9,
    (4, 5): 15,
    (4, 6): 18,
    (4, 7): 18,
    (4, 8): 14,
    (4, 9): 15,
    (4, 10): 22,
    (5, 0): 27,
    (5, 1): 21,
    (5, 2): 18,
    (5, 3): 11,
    (5, 4): 13,
    (5, 6): 9,
    (5, 7): 22,
    (5, 8): 22,
    (5, 9): 12,
    (5, 10): 25,
    (6, 0): 22,
    (6, 1): 15,
    (6, 2): 11,
    (6, 3): 17,
    (6, 4): 16,
    (6, 5): 10,
    (6, 7): 16,
    (6, 8): 20,
    (6, 9): 7,
    (6, 10): 18,
    (7, 0): 6,
    (7, 1): 5,
    (7, 2): 10,
    (7, 3): 21,
    (7, 4): 19,
    (7, 5): 23,
    (7, 6): 17,
    (7, 8): 12,
    (7, 9): 12,
    (7, 10): 7,
    (8, 0): 7,
    (8, 1): 11,
    (8, 2): 20,
    (8, 3): 15,
    (8, 4): 15,
    (8, 5): 22,
    (8, 6): 19,
    (8, 7): 12,
    (8, 9): 16,
    (8, 10): 17,
    (9, 0): 16,
    (9, 1): 10,
    (9, 2): 12,
    (9, 3): 13,
    (9, 4): 12,
    (9, 5): 13,
    (9, 6): 6,
    (9, 7): 11,
    (9, 8): 15,
    (9, 10): 15,
    (10, 0): 13,
    (10, 1): 9,
    (10, 2): 7,
    (10, 3): 26,
    (10, 4): 22,
    (10, 5): 24,
    (10, 6): 16,
    (10, 7): 7,
    (10, 8): 17,
    (10, 9): 16,
    (10, 10): 16,
}

# Define the friends and their availability
friends = {
    "William": {"location": "Alamo Square", "start": 1515, "end": 1715, "duration": 60},
    "Joshua": {"location": "Richmond District", "start": 700, "end": 2000, "duration": 15},
    "Joseph": {"location": "Financial District", "start": 1115, "end": 1330, "duration": 15},
    "David": {"location": "Union Square", "start": 1645, "end": 1915, "duration": 45},
    "Brian": {"location": "Fisherman's Wharf", "start": 1345, "end": 2045, "duration": 105},
    "Karen": {"location": "Marina District", "start": 1130, "end": 1830, "duration": 15},
    "Anthony": {"location": "Haight-Ashbury", "start": 715, "end": 1030, "duration": 30},
    "Matthew": {"location": "Mission District", "start": 1715, "end": 1915, "duration": 120},
    "Helen": {"location": "Pacific Heights", "start": 800, "end": 1200, "duration": 75},
    "Jeffrey": {"location": "Golden Gate Park", "start": 1900, "end": 2130, "duration": 60},
}

# Convert times to minutes from start of the day
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Define the solver
solver = Solver()

# Define the variables
current_location = Int('current_location')
current_time = Int('current_time')
meetings = {}

# Initial conditions
solver.add(current_location == location_indices["The Castro"])
solver.add(current_time == time_to_minutes("09:00"))

# Define the meeting variables and constraints
for i, (friend, details) in enumerate(friends.items()):
    start_time = Int(f'{friend}_start_time')
    end_time = Int(f'{friend}_end_time')
    meetings[friend] = (start_time, end_time)
    
    # Constraints for meeting times
    solver.add(start_time >= details['start'])
    solver.add(end_time <= details['end'])
    solver.add(end_time - start_time >= details['duration'])
    
    # Constraints for travel time
    if i == 0:
        travel_time = Int(f'{friend}_travel_time')
        solver.add(travel_time == travel_times[(current_location, location_indices[details['location']])])
        solver.add(start_time >= current_time + travel_time)
    else:
        prev_friend = list(friends.keys())[i-1]
        prev_end_time = meetings[prev_friend][1]
        travel_time = Int(f'{friend}_travel_time')
        solver.add(travel_time == travel_times[(location_indices[friends[prev_friend]['location']], location_indices[details['location']])])
        solver.add(start_time >= prev_end_time + travel_time)
    
    # Update current location and time
    current_location = location_indices[details['location']]
    current_time = end_time

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend, (start_var, end_var) in meetings.items():
        start_time = model[start_var].as_long()
        end_time = model[end_var].as_long()
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
            "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print(f"SOLUTION: {json.dumps({'itinerary': itinerary})}")
else:
    print("No solution found")