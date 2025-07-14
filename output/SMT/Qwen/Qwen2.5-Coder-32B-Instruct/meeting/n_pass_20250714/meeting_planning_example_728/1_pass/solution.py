from z3 import *

# Define the locations
locations = ["Marina District", "Mission District", "Fisherman's Wharf", "Presidio", 
             "Union Square", "Sunset District", "Financial District", "Haight-Ashbury", "Russian Hill"]

# Define the travel times in minutes
travel_times = {
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Russian Hill"): 15,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Russian Hill"): 24,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Russian Hill"): 11,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Haight-Ashbury"): 17,
}

# Define the friends and their availability
friends = {
    "Karen": {"location": "Mission District", "start": 14*60 + 15, "end": 22*60, "min_time": 30},
    "Richard": {"location": "Fisherman's Wharf", "start": 14*60 + 30, "end": 17*60, "min_time": 30},
    "Robert": {"location": "Presidio", "start": 21*60 + 45, "end": 22*60 + 45, "min_time": 60},
    "Joseph": {"location": "Union Square", "start": 11*60 + 45, "end": 14*60 + 45, "min_time": 120},
    "Helen": {"location": "Sunset District", "start": 14*60 + 45, "end": 20*60 + 45, "min_time": 105},
    "Elizabeth": {"location": "Financial District", "start": 10*60, "end": 12*60 + 45, "min_time": 75},
    "Kimberly": {"location": "Haight-Ashbury", "start": 14*60 + 15, "end": 17*60, "min_time": 105},
    "Ashley": {"location": "Russian Hill", "start": 11*60 + 30, "end": 21*60 + 30, "min_time": 45},
}

# Create the solver
solver = Solver()

# Define the variables
arrival_time = Int('arrival_time')
current_location = String('current_location')

# Initialize the arrival time and location
solver.add(arrival_time == 9*60)  # 9:00 AM
solver.add(current_location == "Marina District")

# Define the visit times for each friend
visit_times = {friend: Int(f'visit_{friend}') for friend in friends}

# Add constraints for each friend
for friend, details in friends.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_time = details["min_time"]
    
    # Friend must be visited within their available time
    solver.add(visit_times[friend] >= start)
    solver.add(visit_times[friend] <= end - min_time)
    
    # Travel time to the friend's location
    travel_time_to_friend = travel_times[(current_location.as_string(), loc)]
    
    # Ensure we have enough time to travel and meet the friend
    solver.add(arrival_time + travel_time_to_friend <= visit_times[friend])
    
    # Update the current location and arrival time after meeting the friend
    current_location = loc
    arrival_time = visit_times[friend] + min_time

# Objective: Maximize the number of friends met
objective = Sum([If(visit_times[friend] >= friends[friend]["start"], 1, 0) for friend in friends])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = [(friend, model.evaluate(visit_times[friend])) for friend in friends]
    solution.sort(key=lambda x: x[1].as_long())
    print("SOLUTION:")
    for friend, time in solution:
        print(f"Meet {friend} at {time.as_long() // 60}:{time.as_long() % 60:02d}")
else:
    print("No solution found")