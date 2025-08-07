from z3 import *

# Define the locations and their travel times
locations = ["Nob Hill", "Presidio", "North Beach", "Fisherman's Wharf", "Pacific Heights"]
travel_times = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 17,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

# Define the friends and their availability
friends = {
    "Jeffrey": {"location": "Presidio", "start": 8*60, "end": 10*60, "min_duration": 105},
    "Steven": {"location": "North Beach", "start": 13*60 + 30, "end": 22*60, "min_duration": 45},
    "Barbara": {"location": "Fisherman's Wharf", "start": 18*60, "end": 21*30, "min_duration": 30},
    "John": {"location": "Pacific Heights", "start": 9*60, "end": 13*30, "min_duration": 15},
}

# Create a solver instance
solver = Solver()

# Define the variables
current_location = String("current_location")
current_time = Int("current_time")
meetings = {name: Bool(name) for name in friends}

# Initial conditions
solver.add(current_location == "Nob Hill")
solver.add(current_time == 9*60)

# Define the constraints for each friend
for name, details in friends.items():
    location = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # Define the meeting start and end times
    meeting_start = Int(f"{name}_start")
    meeting_end = Int(f"{name}_end")
    
    # Constraints for meeting with the friend
    solver.add(Implies(meetings[name], meeting_start >= start))
    solver.add(Implies(meetings[name], meeting_end <= end))
    solver.add(Implies(meetings[name], meeting_end - meeting_start >= min_duration))
    
    # Constraints for travel to the friend's location
    travel_time = Int(f"travel_time_{name}")
    solver.add(travel_time == travel_times[("Nob Hill", location)])
    solver.add(Implies(meetings[name], meeting_start == current_time + travel_time))
    
    # Update the current location and time after the meeting
    solver.add(Implies(meetings[name], current_location == location))
    solver.add(Implies(meetings[name], current_time == meeting_end))
    
    # Ensure no overlapping meetings
    for other_name in friends:
        if other_name != name:
            other_meeting_start = Int(f"{other_name}_start")
            other_meeting_end = Int(f"{other_name}_end")
            solver.add(Or(meeting_end <= other_meeting_start, other_meeting_end <= meeting_start))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, details in friends.items():
        if model.evaluate(meetings[name]):
            start = model.evaluate(Int(f"{name}_start")).as_long()
            end = model.evaluate(Int(f"{name}_end")).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start//60:02}:{start%60:02}",
                "end_time": f"{end//60:02}:{end%60:02}"
            })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")