from z3 import *

# Define the locations and their travel times
locations = ["Nob Hill", "Presidio", "North Beach", "Fisherman's Wharf", "Pacific Heights"]
travel_times = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
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
meeting_times = {name: (Int(f"{name}_start"), Int(f"{name}_end")) for name in friends}

# Initial conditions
solver.add(current_location == "Nob Hill")
solver.add(current_time == 9*60)

# Define the constraints for each friend
for name, details in friends.items():
    location = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    meet = meetings[name]
    meet_start, meet_end = meeting_times[name]
    
    # If we meet the friend, we must be at their location within their availability
    solver.add(Implies(meet, current_location == location))
    solver.add(Implies(meet, meet_start >= start))
    solver.add(Implies(meet, meet_end <= end))
    solver.add(Implies(meet, meet_end - meet_start >= min_duration))
    
    # If we meet the friend, we must have enough time to travel to their location
    for prev_location in locations:
        if prev_location != location:
            travel_time = travel_times[(prev_location, location)]
            solver.add(Implies(And(meet, current_location == prev_location), meet_start >= current_time + travel_time))
    
    # Update current time and location after meeting
    solver.add(Implies(meet, current_time == meet_end))
    solver.add(Implies(meet, current_location == location))

# Define the constraints for travel times
for i, (name1, details1) in enumerate(friends.items()):
    for name2, details2 in list(friends.items())[i+1:]:
        meet1 = meetings[name1]
        meet2 = meetings[name2]
        location1 = details1["location"]
        location2 = details2["location"]
        travel_time = travel_times[(location1, location2)]
        
        # If we meet both friends, we must have enough time to travel between them
        solver.add(Implies(And(meet1, meet2), meeting_times[name2][0] >= meeting_times[name1][1] + travel_time))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, meet in meetings.items():
        if model.evaluate(meet):
            meet_start, meet_end = meeting_times[name]
            start_time = model.evaluate(meet_start).as_long()
            end_time = model.evaluate(meet_end).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_time//60:02}:{start_time%60:02}",
                "end_time": f"{end_time//60:02}:{end_time%60:02}"
            })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")