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
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Haight-Ashbury"): 18,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19
}

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

# Define the start time in minutes since midnight
start_time = 540  # 9:00 AM

# Define the current location
current_location = "Union Square"
current_time = start_time

# Define the total number of friends met
total_friends_met = Int("total_friends_met")
solver.add(total_friends_met == Sum([If(met_friends[friend], 1, 0) for friend in friends]))

# Define the constraint to meet exactly 7 friends
solver.add(total_friends_met == 7)

# Define the constraints for each friend
for friend, details in friends.items():
    location = details["location"]
    start = details["start"]
    end = details["end"]
    duration = details["duration"]
    
    # Calculate the time available to meet the friend
    time_available = end - start - duration
    
    # Constraint to meet the friend within their availability
    meet_constraint = And(
        current_time + travel_times[(current_location, location)] + duration <= end,
        current_time + travel_times[(current_location, location)] >= start
    )
    
    # Add the constraint to the solver
    solver.add(Implies(met_friends[friend], meet_constraint))
    
    # Update the current time if the friend is met
    new_current_time = Int(f"new_current_time_{friend}")
    solver.add(new_current_time == current_time + travel_times[(current_location, location)] + duration)
    
    # Ensure the new current time does not exceed the end time of the day (23:59 -> 1439 minutes)
    solver.add(new_current_time <= 1439)
    
    # Update the current location and time
    current_location = location
    current_time = new_current_time

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    met_list = [friend for friend in friends if model.evaluate(met_friends[friend])]
    print("SOLUTION:", met_list)
else:
    print("No solution found")