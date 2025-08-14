from z3 import *

# Define the locations and their travel times
locations = [
    "Union Square", "Mission District", "Fisherman's Wharf", "Russian Hill",
    "Marina District", "North Beach", "Chinatown", "Pacific Heights",
    "The Castro", "Nob Hill", "Sunset District"
]

travel_times = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    # Add all other travel times similarly
}

# Reverse travel times
for (start, end) in list(travel_times.keys()):
    travel_times[(end, start)] = travel_times[(start, end)]

# Define the meetings and their constraints
meetings = {
    "Kevin": {"location": "Mission District", "start": 2045, "end": 2145, "duration": 60},
    "Mark": {"location": "Fisherman's Wharf", "start": 1715, "end": 2000, "duration": 90},
    "Jessica": {"location": "Russian Hill", "start": 900, "end": 1500, "duration": 120},
    "Jason": {"location": "Marina District", "start": 1515, "end": 2145, "duration": 120},
    "John": {"location": "North Beach", "start": 945, "end": 1800, "duration": 15},
    "Karen": {"location": "Chinatown", "start": 1645, "end": 1900, "duration": 75},
    "Sarah": {"location": "Pacific Heights", "start": 1730, "end": 1815, "duration": 45},
    "Amanda": {"location": "The Castro", "start": 2000, "end": 2115, "duration": 60},
    "Nancy": {"location": "Nob Hill", "start": 945, "end": 1300, "duration": 45},
    "Rebecca": {"location": "Sunset District", "start": 845, "end": 1500, "duration": 75},
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a Z3 solver
solver = Solver()

# Define variables for the start time of each meeting
meeting_vars = {name: Int(name) for name in meetings}

# Add constraints for each meeting
for name, details in meetings.items():
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    duration = details["duration"]
    solver.add(meeting_vars[name] >= start)
    solver.add(meeting_vars[name] + duration <= end)

# Add constraints for travel times
current_location = "Union Square"
current_time = time_to_minutes(900)  # 9:00 AM

# Sort meetings by their start time to try to respect the order
sorted_meetings = sorted(meetings.items(), key=lambda x: x[1]["start"])

for name, details in sorted_meetings:
    location = details["location"]
    duration = details["duration"]
    travel_time = travel_times[(current_location, location)]
    solver.add(meeting_vars[name] >= current_time + travel_time)
    current_time = meeting_vars[name] + duration
    current_location = location

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, details in sorted_meetings:
        start_time = model[meeting_vars[name]].as_long()
        end_time = start_time + details["duration"]
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
            "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")