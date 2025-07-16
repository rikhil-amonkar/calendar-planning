from itertools import combinations
from z3 import *

# Define the locations
locations = ["Fisherman's Wharf", "The Castro", "Golden Gate Park", "Embarcadero", 
             "Russian Hill", "Nob Hill", "Alamo Square", "North Beach"]

# Define the travel times
travel_times = {
    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "North Beach"): 20,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "North Beach"): 5,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Alamo Square"): 16,
}

# Define the friends and their availability
friends = {
    "Laura": {"location": "The Castro", "start": 1945, "end": 2130, "min_time": 105},
    "Daniel": {"location": "Golden Gate Park", "start": 2115, "end": 2145, "min_time": 15},
    "William": {"location": "Embarcadero", "start": 700, "end": 900, "min_time": 90},
    "Karen": {"location": "Russian Hill", "start": 1430, "end": 1945, "min_time": 30},
    "Stephanie": {"location": "Nob Hill", "start": 730, "end": 930, "min_time": 45},
    "Joseph": {"location": "Alamo Square", "start": 1130, "end": 1245, "min_time": 15},
    "Kimberly": {"location": "North Beach", "start": 1545, "end": 1915, "min_time": 30},
}

# Function to check if a combination of friends is feasible
def is_feasible(friends_subset):
    solver = Solver()
    
    # Define variables for the start time of each location visit
    visit_start_times = {loc: Int(f"visit_start_{loc}") for loc in locations}
    
    # Initial constraint: Start at Fisherman's Wharf at 9:00 AM (900 minutes)
    solver.add(visit_start_times["Fisherman's Wharf"] == 900)
    
    # Define binary variables to indicate whether we meet each friend
    meet_friends = {friend: Bool(f"meet_{friend}") for friend in friends_subset}
    
    # Define variables for the duration of stay at each location
    stay_durations = {friend: Int(f"stay_duration_{friend}") for friend in friends_subset}
    
    # Add constraints for each friend
    for friend, info in friends_subset.items():
        loc = info["location"]
        start = info["start"]
        end = info["end"]
        min_time = info["min_time"]
        
        # Constraint: Stay duration must be at least the minimum required time if we meet the friend
        solver.add(stay_durations[friend] >= min_time)
        
        # Constraint: Cannot leave the location before the friend arrives if we meet them
        solver.add(visit_start_times[loc] + stay_durations[friend] <= end)
        
        # Constraint: Must arrive at the location before the friend leaves if we meet them
        solver.add(visit_start_times[loc] >= start)
        
        # Constraint: Travel time to the next location must be considered if we meet them
        for next_loc in locations:
            if next_loc != loc:
                solver.add(visit_start_times[next_loc] >= visit_start_times[loc] + stay_durations[friend] + travel_times[(loc, next_loc)])
    
    # Check if the problem is solvable
    return solver.check() == sat

# Check all combinations of 4 friends
for combo in combinations(friends.items(), 4):
    friends_subset = dict(combo)
    if is_feasible(friends_subset):
        print("SOLUTION:")
        for friend, info in friends_subset.items():
            loc = info["location"]
            start = info["start"]
            end = info["end"]
            min_time = info["min_time"]
            print(f"Meet {friend} at {loc} from {start // 100}:{start % 100:02d} to {end // 100}:{end % 100:02d}")
        break
else:
    print("No solution found.")