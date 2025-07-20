from z3 import *

# Define the locations and their travel times
locations = ["Fisherman's Wharf", "Presidio", "Richmond District", "Financial District"]
travel_times = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21
}

# Define the friends and their availability
friends = {
    "Emily": {"location": "Presidio", "start": 16.25, "end": 21.00, "min_duration": 105/60},
    "Joseph": {"location": "Richmond District", "start": 17.25, "end": 22.00, "min_duration": 120/60},
    "Melissa": {"location": "Financial District", "start": 15.75, "end": 19.75, "min_duration": 75/60}
}

# Create a solver instance
solver = Solver()

# Define the start time for each friend meeting
start_times = {friend: Real(f"start_{friend}") for friend in friends}

# Define the end time for each friend meeting
end_times = {friend: Real(f"end_{friend}") for friend in friends}

# Define the current location
current_location = "Fisherman's Wharf"
current_time = 9.00

# Add constraints for each friend
for friend, details in friends.items():
    # Friend must be met within their availability
    solver.add(start_times[friend] >= details["start"])
    solver.add(end_times[friend] <= details["end"])
    # Meeting duration must be at least the minimum required
    solver.add(end_times[friend] - start_times[friend] >= details["min_duration"])
    # Travel time to the friend's location
    travel_time = travel_times[(current_location, details["location"])]
    solver.add(start_times[friend] >= current_time + travel_time/60)
    # Update current time and location after meeting
    current_time = end_times[friend]
    current_location = details["location"]

# Function to convert time in hours to HH:MM format
def time_to_str(time):
    hours = int(time)
    minutes = int((time - hours) * 60)
    return f"{hours:02}:{minutes:02}"

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend in friends:
        start = model[start_times[friend]].as_real().numerator() / model[start_times[friend]].as_real().denominator()
        end = model[end_times[friend]].as_real().numerator() / model[end_times[friend]].as_real().denominator()
        itinerary.append({"action": "meet", "person": friend, "start_time": time_to_str(start), "end_time": time_to_str(end)})
    print({"itinerary": itinerary})
else:
    print("No solution found")