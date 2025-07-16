from z3 import *

# Define the locations
locations = ["Pacific Heights", "Golden Gate Park", "The Castro", "Bayview",
             "Marina District", "Union Square", "Sunset District", "Alamo Square",
             "Financial District", "Mission District"]

# Define the travel times (in minutes)
travel_times = {
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Mission District"): 17,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Mission District"): 7,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Mission District"): 13,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Mission District"): 20,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Mission District"): 14,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 10,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 16,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
}

# Define the friends and their availability
friends = {
    "Helen": {"location": "Golden Gate Park", "start": 9*60 + 30, "end": 12*60 + 15, "min_duration": 45},
    "Steven": {"location": "The Castro", "start": 20*60 + 15, "end": 22*60, "min_duration": 105},
    "Deborah": {"location": "Bayview", "start": 8*60 + 30, "end": 12*60, "min_duration": 30},
    "Matthew": {"location": "Marina District", "start": 9*60 + 15, "end": 14*60 + 15, "min_duration": 45},
    "Joseph": {"location": "Union Square", "start": 14*60 + 15, "end": 18*60 + 45, "min_duration": 120},
    "Ronald": {"location": "Sunset District", "start": 16*60, "end": 20*60 + 45, "min_duration": 60},
    "Robert": {"location": "Alamo Square", "start": 18*60 + 30, "end": 21*60 + 15, "min_duration": 120},
    "Rebecca": {"location": "Financial District", "start": 14*60 + 45, "end": 16*60 + 15, "min_duration": 30},
    "Elizabeth": {"location": "Mission District", "start": 18*60 + 30, "end": 21*60, "min_duration": 120},
}

# Create a solver instance
solver = Solver()

# Define the variables for the time spent with each friend
time_with_friends = {friend: Int(f"time_with_{friend}") for friend in friends}

# Define the variables for the arrival time at each location
arrival_times = {location: Int(f"arrival_at_{location}") for location in locations}

# Set the initial arrival time at Pacific Heights
solver.add(arrival_times["Pacific Heights"] == 9*60)

# Add constraints for each friend
for friend, details in friends.items():
    location = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # Define the arrival and departure times for the friend
    arrival = arrival_times[location]
    departure = arrival + min_duration
    
    # Ensure the friend is available during the meeting
    solver.add(arrival >= start)
    solver.add(departure <= end)
    
    # Ensure the meeting duration is at least the minimum required
    solver.add(time_with_friends[friend] == min_duration)

# Add constraints for travel times between locations
for i in range(len(locations)):
    for j in range(i + 1, len(locations)):
        loc1, loc2 = locations[i], locations[j]
        travel_time = travel_times[(loc1, loc2)]
        
        # If moving from loc1 to loc2, ensure the arrival time at loc2 is after the departure from loc1
        solver.add(Or(arrival_times[loc1] + travel_time >= arrival_times[loc2],
                     arrival_times[loc2] + travel_time >= arrival_times[loc1]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, details in friends.items():
        print(f"Meet {friend} at {details['location']} for {details['min_duration']} minutes.")
    for location, time in arrival_times.items():
        arrival_time_minutes = model[time].as_long()
        hours = arrival_time_minutes // 60
        minutes = arrival_time_minutes % 60
        print(f"Arrive at {location} at {hours:02}:{minutes:02} AM/PM.")
else:
    print("No solution found.")