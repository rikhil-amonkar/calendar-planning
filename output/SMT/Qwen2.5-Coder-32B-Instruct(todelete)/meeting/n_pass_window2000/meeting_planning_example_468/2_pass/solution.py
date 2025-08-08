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

# Create a solver
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_times = {}
for friend in friends:
    meeting_times[friend] = (Int(f"{friend}_start"), Int(f"{friend}_end"))

# Define the start time at The Castro
start_time = 9*60  # 9:00 AM

# Add constraints for each friend
for friend, (start, end) in meeting_times.items():
    friend_info = friends[friend]
    # Meeting must be within the friend's availability
    solver.add(start >= friend_info["start"])
    solver.add(end <= friend_info["end"])
    # Meeting must be at least 90 minutes
    solver.add(end - start >= 90)

# Add constraints for travel times
for i, friend1 in enumerate(friends):
    for j, friend2 in enumerate(friends):
        if i < j:
            start1, end1 = meeting_times[friend1]
            start2, end2 = meeting_times[friend2]
            loc1 = friends[friend1]["location"]
            loc2 = friends[friend2]["location"]
            travel_time1 = travel_times[(loc1, loc2)]
            travel_time2 = travel_times[(loc2, loc1)]
            # If meeting with friend1 ends before meeting with friend2 starts, add travel time constraint
            solver.add(Or(end1 + travel_time1 <= start2, end2 + travel_time2 <= start1))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend, (start, end) in meeting_times.items():
        start_time_minutes = model[start].as_long()
        end_time_minutes = model[end].as_long()
        start_time_str = f"{start_time_minutes // 60:02}:{start_time_minutes % 60:02}"
        end_time_str = f"{end_time_minutes // 60:02}:{end_time_minutes % 60:02}"
        itinerary.append({"action": "meet", "person": friend, "start_time": start_time_str, "end_time": end_time_str})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")