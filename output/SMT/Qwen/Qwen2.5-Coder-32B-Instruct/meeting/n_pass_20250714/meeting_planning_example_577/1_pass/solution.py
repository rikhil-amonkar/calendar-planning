from z3 import *

# Define the locations
locations = ["Haight-Ashbury", "Russian Hill", "Fisherman's Wharf", "Nob Hill", 
             "Golden Gate Park", "Alamo Square", "Pacific Heights"]

# Define the travel times as a dictionary
travel_times = {
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
}

# Define the friends' availability
friends_availability = {
    "Stephanie": ("Russian Hill", 20*60, 20*60 + 45),  # 8:00PM to 8:45PM
    "Kevin": ("Fisherman's Wharf", 19*60 + 15, 21*60 + 45),  # 7:15PM to 9:45PM
    "Robert": ("Nob Hill", 7*60 + 45, 10*60 + 30),  # 7:45AM to 10:30AM
    "Steven": ("Golden Gate Park", 8*60 + 30, 17*60),  # 8:30AM to 5:00PM
    "Anthony": ("Alamo Square", 7*60 + 45, 19*60 + 45),  # 7:45AM to 7:45PM
    "Sandra": ("Pacific Heights", 14*60 + 45, 21*60 + 45),  # 2:45PM to 9:45PM
}

# Define the minimum meeting times
min_meeting_times = {
    "Stephanie": 15,
    "Kevin": 75,
    "Robert": 90,
    "Steven": 75,
    "Anthony": 15,
    "Sandra": 45,
}

# Create a solver instance
solver = Solver()

# Define the arrival time variables for each location
arrival_times = {location: Int(f"arrival_{location}") for location in locations}

# Add constraints for the initial arrival time
solver.add(arrival_times["Haight-Ashbury"] == 9*60)  # 9:00AM

# Add constraints for travel times
for (loc1, loc2), time in travel_times.items():
    solver.add(arrival_times[loc2] >= arrival_times[loc1] + time)

# Add constraints for meeting friends
for friend, (location, start_time, end_time) in friends_availability.items():
    min_meeting_time = min_meeting_times[friend]
    solver.add(arrival_times[location] + min_meeting_time <= end_time)
    solver.add(arrival_times[location] <= start_time + (end_time - start_time) - min_meeting_time)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    schedule = [(location, model[arrival_times[location]].as_long()) for location in locations]
    schedule.sort(key=lambda x: x[1])
    print("SOLUTION:")
    for location, time in schedule:
        print(f"{location}: {time//60}:{time%60:02d}")
else:
    print("No solution found.")