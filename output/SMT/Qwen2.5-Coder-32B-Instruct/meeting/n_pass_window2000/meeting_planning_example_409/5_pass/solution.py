from z3 import *

# Define the locations
locations = ["Fisherman's Wharf", "Bayview", "Golden Gate Park", "Nob Hill", "Marina District", "Embarcadero"]

# Define the travel times in minutes
travel_times = {
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Embarcadero"): 19,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Embarcadero"): 9,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
}

# Define the friends and their availability
friends = {
    "Thomas": {"location": "Bayview", "start": 1530, "end": 1830, "min_duration": 120},
    "Stephanie": {"location": "Golden Gate Park", "start": 1830, "end": 2145, "min_duration": 30},
    "Laura": {"location": "Nob Hill", "start": 845, "end": 1615, "min_duration": 30},
    "Betty": {"location": "Marina District", "start": 1845, "end": 2145, "min_duration": 45},
    "Patricia": {"location": "Embarcadero", "start": 1730, "end": 2200, "min_duration": 45},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {name: Int(f"{name}_start") for name in friends}
meeting_end = {name: Int(f"{name}_end") for name in friends}

# Define the current location and time
current_location = "Fisherman's Wharf"
current_time = time_to_minutes(900)  # 9:00 AM

# Add constraints for each friend
for name, details in friends.items():
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    location = details["location"]
    
    # Meeting must start after the current time and within the friend's availability
    solver.add(meeting_start[name] >= current_time)
    solver.add(meeting_start[name] >= start_time)
    solver.add(meeting_end[name] <= end_time)
    
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= min_duration)
    
    # Travel time to the friend's location
    travel_time = travel_times[(current_location, location)]
    solver.add(meeting_start[name] >= current_time + travel_time)
    
    # Update current time and location
    current_time = meeting_end[name]
    current_location = location

# Define the order of meetings
order_vars = {name: Int(f"{name}_order") for name in friends}
for i, name1 in enumerate(friends):
    for j, name2 in enumerate(friends):
        if i < j:
            solver.add(order_vars[name1] < order_vars[name2])

# Add constraints for the order of meetings and travel times
for i, name1 in enumerate(friends):
    for j, name2 in enumerate(friends):
        if i < j:
            # If meeting with name1 is before meeting with name2
            with_meeting1_before_meeting2 = And(order_vars[name1] < order_vars[name2])
            # Ensure travel time from name1's location to name2's location
            travel_time = travel_times[(friends[name1]["location"], friends[name2]["location"])]
            solver.add(Implies(with_meeting1_before_meeting2, meeting_start[name2] >= meeting_end[name1] + travel_time))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[meeting_start[name]].as_long()
        end = model[meeting_end[name]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(int(x["start_time"].replace(":", ""))))
    print({"itinerary": itinerary})
else:
    print("No feasible schedule found")