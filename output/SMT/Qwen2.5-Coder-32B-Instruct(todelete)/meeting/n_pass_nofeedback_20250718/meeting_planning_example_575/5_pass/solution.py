from z3 import *

# Define the locations
locations = ["The Castro", "Presidio", "Sunset District", "Haight-Ashbury", "Mission District", "Golden Gate Park", "Russian Hill"]

# Define the travel times in minutes
travel_times = {
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Russian Hill"): 18,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Russian Hill"): 14,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Russian Hill"): 24,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Russian Hill"): 15,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Golden Gate Park"): 21,
}

# Define the people and their availability
people = {
    "Rebecca": {"location": "Presidio", "start": 1815, "end": 2045, "duration": 60},
    "Linda": {"location": "Sunset District", "start": 1530, "end": 1945, "duration": 30},
    "Elizabeth": {"location": "Haight-Ashbury", "start": 1715, "end": 1930, "duration": 105},
    "William": {"location": "Mission District", "start": 1315, "end": 1930, "duration": 30},
    "Robert": {"location": "Golden Gate Park", "start": 1415, "end": 2130, "duration": 45},
    "Mark": {"location": "Russian Hill", "start": 1000, "end": 2115, "duration": 75},
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver
solver = Solver()

# Define variables
meetings = []
current_time = time_to_minutes(900)  # Start at 9:00 AM

# Define meeting variables and constraints
for person, details in people.items():
    start_time = Int(f'start_{person}')
    end_time = Int(f'end_{person}')
    meetings.append((person, start_time, end_time))
    
    # Constraints for meeting times
    solver.add(start_time >= time_to_minutes(details["start"]))
    solver.add(end_time <= time_to_minutes(details["end"]))
    solver.add(end_time - start_time >= details["duration"])
    
    # Constraints for travel time
    if meetings:
        prev_person, prev_start, prev_end = meetings[-2]
        solver.add(prev_end + travel_times[(people[prev_person]["location"], details["location"])] <= start_time)
        solver.add(prev_end + travel_times[(people[prev_person]["location"], details["location"])] + details["duration"] <= end_time)
    else:
        # First meeting, start from The Castro
        solver.add(start_time >= current_time + travel_times[("The Castro", details["location"])])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, start_var, end_var in meetings:
        start_time = model[start_var].as_long()
        end_time = model[end_var].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
            "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")