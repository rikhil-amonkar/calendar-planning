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

# Define variables for each friend's meeting start and end times
meeting_vars = {}
for friend, details in friends.items():
    start = Int(f"{friend}_start")
    end = Int(f"{friend}_end")
    meeting_vars[friend] = (start, end)
    solver.add(start >= time_to_minutes(details["start"]))
    solver.add(end <= time_to_minutes(details["end"]))
    solver.add(end - start >= details["min_duration"])

# Define a variable for the current time
current_time = Int("current_time")
solver.add(current_time == time_to_minutes(900))  # Start at 9:00 AM

# Define a variable for the current location
current_location = "Embarcadero"

# Add constraints for each friend's meeting
for friend, details in friends.items():
    start, end = meeting_vars[friend]
    location = details["location"]
    
    # Ensure we can travel to the next location in time
    if current_location != location:
        solver.add(current_time + travel_times[(current_location, location)] <= start)
    
    # Update current time and location
    current_time = end
    current_location = location

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend, details in friends.items():
        start = model[meeting_vars[friend][0]].as_long()
        end = model[meeting_vars[friend][1]].as_long()
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    itinerary.sort(key=lambda x: time_to_minutes(int(x["start_time"].replace(":", ""))))
    print({"itinerary": itinerary})
else:
    print("No feasible schedule found")