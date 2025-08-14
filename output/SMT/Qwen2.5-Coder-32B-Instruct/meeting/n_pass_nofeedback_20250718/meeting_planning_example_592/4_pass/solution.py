from z3 import *
from itertools import permutations

# Define the locations and their travel times
locations = ["North Beach", "Pacific Heights", "Chinatown", "Union Square", "Mission District", "Golden Gate Park", "Nob Hill"]
travel_times = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Nob Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Nob Hill"): 8,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Nob Hill"): 9,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Nob Hill"): 12,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
}

# Define the friends and their availability
friends = {
    "James": {"location": "Pacific Heights", "start": 2000, "end": 2200, "duration": 120},
    "Robert": {"location": "Chinatown", "start": 1215, "end": 1645, "duration": 90},
    "Jeffrey": {"location": "Union Square", "start": 930, "end": 1530, "duration": 120},
    "Carol": {"location": "Mission District", "start": 1815, "end": 2115, "duration": 15},
    "Mark": {"location": "Golden Gate Park", "start": 1130, "end": 1745, "duration": 15},
    "Sandra": {"location": "Nob Hill", "start": 800, "end": 1530, "duration": 15},
}

# Convert times to minutes from 00:00
def time_to_minutes(time):
    return time // 100 * 60 + time % 100

# Function to check if a given sequence of meetings is feasible
def is_feasible(sequence):
    solver = Solver()
    
    # Define variables for the start time of each meeting
    meeting_times = {name: Int(f"start_{name}") for name in sequence}
    
    # Add constraints for each friend
    for name in sequence:
        details = friends[name]
        start = meeting_times[name]
        duration = details["duration"]
        solver.add(start >= time_to_minutes(details["start"]))
        solver.add(start + duration <= time_to_minutes(details["end"]))
    
    # Define the current location and time
    current_location = "North Beach"
    current_time = time_to_minutes(900)  # 9:00 AM
    
    # Add constraints for travel times and meeting sequences
    for i in range(len(sequence)):
        name = sequence[i]
        location = friends[name]["location"]
        start = meeting_times[name]
        duration = friends[name]["duration"]
        
        # Ensure the meeting starts after traveling to the location
        solver.add(start >= current_time + travel_times[(current_location, location)])
        
        # Update the current location and time after the meeting
        current_location = location
        current_time = start + duration
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in sequence:
            start_time = model[meeting_times[name]].as_long()
            end_time = start_time + friends[name]["duration"]
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
                "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
            })
        itinerary.sort(key=lambda x: x["start_time"])
        return itinerary
    else:
        return None

# Generate all permutations of friends
friends_list = list(friends.keys())
for sequence in permutations(friends_list):
    itinerary = is_feasible(sequence)
    if itinerary:
        print({"itinerary": itinerary})
        break
else:
    print("No solution found")