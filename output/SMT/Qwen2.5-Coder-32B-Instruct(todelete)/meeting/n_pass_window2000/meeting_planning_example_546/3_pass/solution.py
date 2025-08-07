from z3 import *

# Define the locations and their travel times
locations = ["Embarcadero", "Richmond District", "Union Square", "Financial District", "Pacific Heights", "Nob Hill", "Bayview"]
travel_times = {
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Bayview"): 21,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 26,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Bayview"): 19,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Bayview"): 22,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Bayview"): 19,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20,
}

# Define the friends and their availability
friends = {
    "Kenneth": {"location": "Richmond District", "start": 2115, "end": 2400, "min_duration": 30},
    "Lisa": {"location": "Union Square", "start": 900, "end": 1630, "min_duration": 45},
    "Joshua": {"location": "Financial District", "start": 1200, "end": 1515, "min_duration": 15},
    "Nancy": {"location": "Pacific Heights", "start": 800, "end": 1130, "min_duration": 90},
    "Andrew": {"location": "Nob Hill", "start": 1130, "end": 2015, "min_duration": 60},
    "John": {"location": "Bayview", "start": 1645, "end": 2130, "min_duration": 75},
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {name: Int(f"start_{name}") for name in friends}
meeting_end = {name: Int(f"end_{name}") for name in friends}

# Define variables for the location of each meeting
meeting_location = {name: String(f"location_{name}") for name in friends}

# Add constraints for each friend
for name, details in friends.items():
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    location = details["location"]
    
    # Meeting must start after arrival and end before leaving
    solver.add(meeting_start[name] >= 540)  # 9:00 AM
    solver.add(meeting_end[name] <= 1440)   # 24:00 (end of day)
    
    # Meeting must be within the friend's availability
    solver.add(meeting_start[name] >= start_time)
    solver.add(meeting_end[name] <= end_time)
    
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[name] - meeting_start[name] >= min_duration)
    
    # Meeting must be at the correct location
    solver.add(meeting_location[name] == location)

# Add constraints for travel times between meetings
friends_list = list(friends.keys())
for i in range(len(friends_list)):
    for j in range(i + 1, len(friends_list)):
        name1 = friends_list[i]
        name2 = friends_list[j]
        travel_time = travel_times[(friends[name1]["location"], friends[name2]["location"])]
        # If meeting with name1 ends before meeting with name2 starts, add travel time constraint
        solver.add(Or(meeting_end[name1] + travel_time <= meeting_start[name2], meeting_end[name2] + travel_time <= meeting_start[name1]))

# Add constraints to ensure meetings are in chronological order and respect travel times
for i in range(len(friends_list)):
    for j in range(i + 1, len(friends_list)):
        name1 = friends_list[i]
        name2 = friends_list[j]
        travel_time = travel_times[(friends[name1]["location"], friends[name2]["location"])]
        solver.add(meeting_end[name1] + travel_time <= meeting_start[name2])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[meeting_start[name]].as_long()
        end = model[meeting_end[name]].as_long()
        location = model[meeting_location[name]].as_string()[1:-1]  # Remove quotes
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