from z3 import *

# Define the locations
locations = ["Union Square", "Presidio", "Alamo Square", "Marina District", 
             "Financial District", "Nob Hill", "Sunset District", 
             "Chinatown", "Russian Hill", "North Beach", "Haight-Ashbury"]

# Define the travel times in a dictionary
travel_times = {
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Haight-Ashbury"): 18,
    # Add all other travel times similarly...
}

# Add reverse travel times
for (start, end) in list(travel_times.keys()):
    travel_times[(end, start)] = travel_times[(start, end)]

# Define the friends and their availability
friends = {
    "Kimberly": {"location": "Presidio", "start": 1530, "end": 1600, "duration": 15},
    "Elizabeth": {"location": "Alamo Square", "start": 1915, "end": 2015, "duration": 15},
    "Joshua": {"location": "Marina District", "start": 1030, "end": 1415, "duration": 45},
    "Sandra": {"location": "Financial District", "start": 1930, "end": 2015, "duration": 45},
    "Kenneth": {"location": "Nob Hill", "start": 1245, "end": 2145, "duration": 30},
    "Betty": {"location": "Sunset District", "start": 1400, "end": 1900, "duration": 60},
    "Deborah": {"location": "Chinatown", "start": 1715, "end": 2030, "duration": 15},
    "Barbara": {"location": "Russian Hill", "start": 1730, "end": 2115, "duration": 120},
    "Steven": {"location": "North Beach", "start": 1745, "end": 2045, "duration": 90},
    "Daniel": {"location": "Haight-Ashbury", "start": 1830, "end": 1845, "duration": 15}
}

# Create a Z3 solver instance
solver = Solver()

# Define variables for each friend indicating if they are met
met_friends = {friend: Bool(f"met_{friend}") for friend in friends}

# Define variables for the time spent at each location
time_at_location = {location: Int(f"time_at_{location}") for location in locations}

# Define the start time in minutes since midnight
start_time = 540  # 9:00 AM

# Define the current location
current_location = String("current_location")
solver.add(current_location == "Union Square")

# Define the total time spent traveling
total_travel_time = Int("total_travel_time")
solver.add(total_travel_time == 0)

# Define the constraints for each friend
for friend, details in friends.items():
    location = details["location"]
    start = details["start"]
    end = details["end"]
    duration = details["duration"]
    
    # Constraint to meet the friend within their availability
    meet_constraint = And(
        time_at_location[location] + total_travel_time + start_time >= start,
        time_at_location[location] + total_travel_time + start_time <= end - duration
    )
    
    # Add the constraint to the solver
    solver.add(Implies(met_friends[friend], meet_constraint))
    
    # Update the total travel time if the friend is met
    travel_time_to_location = Int(f"travel_time_to_{location}")
    solver.add(travel_time_to_location == travel_times[(current_location, location)])
    solver.add(total_travel_time == total_travel_time + travel_time_to_location)
    
    # Update the current location
    current_location = location
    
    # Update the time spent at the location
    solver.add(time_at_location[location] == duration)

# Maximize the number of friends met
objective = Sum([If(met_friends[friend], 1, 0) for friend in friends])
solver.maximize(objective)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    met_list = [friend for friend in friends if model.evaluate(met_friends[friend])]
    print("SOLUTION:", met_list)
else:
    print("No solution found")