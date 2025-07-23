from z3 import *

# Define the locations and their travel times
locations = ["Fisherman's Wharf", "Golden Gate Park", "Presidio", "Richmond District"]
travel_times = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7,
}

# Define the friends and their availability
friends = {
    "Melissa": {"location": "Golden Gate Park", "start": 8.5, "end": 20.0, "min_duration": 0.25},
    "Nancy": {"location": "Presidio", "start": 19.75, "end": 22.0, "min_duration": 1.75},
    "Emily": {"location": "Richmond District", "start": 16.75, "end": 22.0, "min_duration": 2.0},
}

# Convert times to minutes for easier calculations
def time_to_minutes(time):
    hours, minutes = divmod(time * 60, 60)
    return int(hours) * 60 + int(minutes)

# Create a solver instance
solver = Solver()

# Define the start time at Fisherman's Wharf
start_time = time_to_minutes(9.0)

# Define variables for meeting start and end times
meeting_start = {friend: Int(f"{friend}_start") for friend in friends}
meeting_end = {friend: Int(f"{friend}_end") for friend in friends}

# Add constraints for each friend
for friend, details in friends.items():
    loc = details["location"]
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    min_duration = time_to_minutes(details["min_duration"])
    
    # Meeting must start after arrival and end before leaving
    solver.add(meeting_start[friend] >= start_time + travel_times[("Fisherman's Wharf", loc)])
    solver.add(meeting_end[friend] <= end)
    
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[friend] - meeting_start[friend] >= min_duration)
    
    # Meeting must start after the friend is available
    solver.add(meeting_start[friend] >= start)
    
    # Meeting must end before the friend leaves
    solver.add(meeting_end[friend] <= end)

# Add constraints for travel times between meetings
for i, friend1 in enumerate(friends):
    for friend2 in list(friends.keys())[i+1:]:
        loc1 = friends[friend1]["location"]
        loc2 = friends[friend2]["location"]
        travel_time = travel_times[(loc1, loc2)]
        
        # If meeting with friend1 ends before meeting with friend2 starts, add travel time constraint
        solver.add(Or(meeting_end[friend1] + travel_time <= meeting_start[friend2],
                      meeting_end[friend2] + travel_time <= meeting_start[friend1]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend in friends:
        start = model[meeting_start[friend]].as_long() / 60
        end = model[meeting_end[friend]].as_long() / 60
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": f"{int(start):02}:{int((start % 1) * 60):02}",
            "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")