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

# Define the friends' availability and meeting duration requirements
friends_availability = {
    "Rebecca": ("Presidio", 1815, 2045, 60),  # 6:15PM to 8:45PM, 60 minutes
    "Linda": ("Sunset District", 1530, 1945, 30),  # 3:30PM to 7:45PM, 30 minutes
    "Elizabeth": ("Haight-Ashbury", 1715, 1930, 105),  # 5:15PM to 7:30PM, 105 minutes
    "William": ("Mission District", 1315, 1930, 30),  # 1:15PM to 7:30PM, 30 minutes
    "Robert": ("Golden Gate Park", 1415, 2130, 45),  # 2:15PM to 9:30PM, 45 minutes
    "Mark": ("Russian Hill", 1000, 2115, 75),  # 10:00AM to 9:15PM, 75 minutes
}

# Convert time to minutes since 9:00AM
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return (hours - 9) * 60 + minutes

# Create the solver
solver = Solver()

# Define variables for the time spent at each location
visit_times = {loc: Int(f"visit_time_{loc}") for loc in locations}

# Define boolean variables for visiting each location
visit_flags = {loc: Bool(f"visit_flag_{loc}") for loc in locations}

# Add constraints for visit times
for loc in locations:
    solver.add(Or(visit_times[loc] == 0, visit_flags[loc]))

# Add constraints for travel times
for (start, end), time in travel_times.items():
    solver.add(Implies(And(visit_flags[start], visit_flags[end]), visit_times[end] >= visit_times[start] + time))

# Add constraints for friends' availability and meeting duration
for friend, (location, start_time, end_time, duration) in friends_availability.items():
    start_time_minutes = time_to_minutes(start_time)
    end_time_minutes = time_to_minutes(end_time)
    solver.add(Implies(visit_flags[location], And(visit_times[location] + duration <= end_time_minutes, visit_times[location] >= start_time_minutes)))

# Ensure we visit exactly 6 locations
solver.add(Sum([If(flag, 1, 0) for flag in visit_flags.values()]) == 6)

# Objective: Maximize the number of friends met
# Since we have constraints for meeting durations, we just need to find a feasible solution
if solver.check() == sat:
    model = solver.model()
    schedule = {loc: model.evaluate(visit_times[loc]).as_long() for loc in locations if model.evaluate(visit_flags[loc])}
    print("SOLUTION:")
    for loc, time in sorted(schedule.items(), key=lambda x: x[1]):
        print(f"{loc}: {time // 60 + 9}:{time % 60:02}AM")
else:
    print("No solution found")