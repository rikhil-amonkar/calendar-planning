from z3 import *

# Define the locations
locations = ["Alamo Square", "Russian Hill", "Presidio", "Chinatown", "Sunset District", "The Castro", "Embarcadero", "Golden Gate Park"]

# Define the travel times in minutes
travel_times = {
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Embarcadero"): 31,
    ("Sunset District", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Embarcadero"): 25,
}

# Define the friends and their availability
friends = {
    "Emily": {"location": "Russian Hill", "start": 12*60 + 15, "end": 14*60 + 15, "min_duration": 105},
    "Mark": {"location": "Presidio", "start": 14*60 + 45, "end": 19*60 + 30, "min_duration": 60},
    "Deborah": {"location": "Chinatown", "start": 7*60 + 30, "end": 15*60 + 30, "min_duration": 45},
    "Margaret": {"location": "Sunset District", "start": 21*60 + 30, "end": 22*60 + 30, "min_duration": 60},
    "George": {"location": "The Castro", "start": 7*60 + 30, "end": 14*60 + 15, "min_duration": 60},
    "Andrew": {"location": "Embarcadero", "start": 20*60 + 15, "end": 22*00, "min_duration": 75},
    "Steven": {"location": "Golden Gate Park", "start": 11*60 + 15, "end": 21*60 + 15, "min_duration": 105},
}

# Create a solver
solver = Solver()

# Define the start time of the day in minutes (9:00 AM)
start_time = 9*60

# Define the variables for the start and end times of each meeting
meeting_starts = {name: Int(f"start_{name}") for name in friends}
meeting_ends = {name: Int(f"end_{name}") for name in friends}

# Define the location variables
current_location = "Alamo Square"
current_time = start_time

# Add constraints for each friend
for name, details in friends.items():
    start = meeting_starts[name]
    end = meeting_ends[name]
    location = details["location"]
    availability_start = details["start"]
    availability_end = details["end"]
    min_duration = details["min_duration"]
    
    # Meeting must start after the current time or after the friend's availability start
    solver.add(start >= If(current_time > availability_start, current_time, availability_start))
    # Meeting must end before the friend's availability end
    solver.add(end <= availability_end)
    # Meeting must last at least the minimum duration
    solver.add(end - start >= min_duration)
    # Travel time to the friend's location
    travel_time = travel_times[(current_location, location)]
    solver.add(start >= current_time + travel_time)
    # Update the current location and time
    current_location = location
    current_time = end

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start = model[meeting_starts[name]].as_long()
        end = model[meeting_ends[name]].as_long()
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