from itertools import permutations
from z3 import *

# Define the locations and their travel times
locations = ["The Castro", "Bayview", "Pacific Heights", "Alamo Square", "Fisherman's Wharf", "Golden Gate Park"]
travel_times = {
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Golden Gate Park"): 11,
    ("Bayview", "The Castro"): 20,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
}

# Define the friends and their availability
friends = {
    "Rebecca": {"location": "Bayview", "start": 9*60, "end": 12*60 + 45},
    "Amanda": {"location": "Pacific Heights", "start": 18*60 + 30, "end": 21*60 + 45},
    "James": {"location": "Alamo Square", "start": 9*60 + 45, "end": 21*60 + 15},
    "Sarah": {"location": "Fisherman's Wharf", "start": 8*60, "end": 21*60 + 30},
    "Melissa": {"location": "Golden Gate Park", "start": 9*60, "end": 18*60 + 45},
}

# Function to check if a given permutation of friends is feasible
def is_feasible(permutation):
    solver = Solver()
    current_location = "The Castro"
    current_time = 9*60  # Start at 9:00 AM

    meeting_times = {}
    for friend in permutation:
        meeting_times[friend] = (Int(f"{friend}_start"), Int(f"{friend}_end"))

    for friend, (start, end) in meeting_times.items():
        friend_info = friends[friend]
        solver.add(start >= friend_info["start"])
        solver.add(end <= friend_info["end"])
        solver.add(end - start >= 90)  # Minimum 90 minutes meeting
        solver.add(start >= current_time + travel_times[(current_location, friend_info["location"])])
        current_time = end + travel_times[(friend_info["location"], current_location)]
        current_location = friend_info["location"]

    return solver.check() == sat

# Generate all permutations of friends and check each one
friends_list = list(friends.keys())
for perm in permutations(friends_list):
    if is_feasible(perm):
        solver = Solver()
        current_location = "The Castro"
        current_time = 9*60  # Start at 9:00 AM

        meeting_times = {}
        for friend in perm:
            meeting_times[friend] = (Int(f"{friend}_start"), Int(f"{friend}_end"))

        for friend, (start, end) in meeting_times.items():
            friend_info = friends[friend]
            solver.add(start >= friend_info["start"])
            solver.add(end <= friend_info["end"])
            solver.add(end - start >= 90)  # Minimum 90 minutes meeting
            solver.add(start >= current_time + travel_times[(current_location, friend_info["location"])])
            current_time = end + travel_times[(friend_info["location"], current_location)]
            current_location = friend_info["location"]

        model = solver.model()
        itinerary = []
        for friend, (start, end) in meeting_times.items():
            start_time = model[start].as_long()
            end_time = model[end].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
                "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
            })
        itinerary.sort(key=lambda x: x["start_time"])
        print({"itinerary": itinerary})
        break
else:
    print("No solution found")