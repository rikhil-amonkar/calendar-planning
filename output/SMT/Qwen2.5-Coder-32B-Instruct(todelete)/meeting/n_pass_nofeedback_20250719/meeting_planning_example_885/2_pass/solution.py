from z3 import *

# Define the locations and their travel times
locations = ["Russian Hill", "Marina District", "Financial District", "Alamo Square", 
             "Golden Gate Park", "The Castro", "Bayview", "Sunset District", 
             "Haight-Ashbury", "Nob Hill"]

travel_times = {
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Nob Hill"): 5,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Nob Hill"): 8,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Nob Hill"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Nob Hill"): 16,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Nob Hill"): 27,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Haight-Ashbury"): 13,
}

# Define the people and their availability
people = {
    "Mark": ("Marina District", 1845, 2100, 90),
    "Karen": ("Financial District", 930, 1245, 90),
    "Barbara": ("Alamo Square", 1000, 1930, 90),
    "Nancy": ("Golden Gate Park", 1645, 2000, 105),
    "David": ("The Castro", 900, 1800, 120),
    "Linda": ("Bayview", 1815, 1945, 45),
    "Kevin": ("Sunset District", 1000, 1745, 120),
    "Matthew": ("Haight-Ashbury", 1015, 1530, 45),
    "Andrew": ("Nob Hill", 1145, 1645, 105),
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables
start_times = {person: Int(f"start_{person}") for person in people}
end_times = {person: Int(f"end_{person}") for person in people}
current_time = Int("current_time")
current_location = "Russian Hill"

# Initial conditions
solver.add(current_time == time_to_minutes(900))

# Constraints for each person
for person, (location, start, end, duration) in people.items():
    start_minutes = time_to_minutes(start)
    end_minutes = time_to_minutes(end)
    solver.add(start_times[person] >= start_minutes)
    solver.add(end_times[person] <= end_minutes)
    solver.add(end_times[person] - start_times[person] >= duration)
    solver.add(current_time + travel_times[(current_location, location)] <= start_times[person])
    solver.add(current_time + travel_times[(current_location, location)] + duration <= end_minutes)
    solver.add(current_time + travel_times[(current_location, location)] + duration <= 1440)  # End of day
    current_time = end_times[person]
    current_location = location

# Optimize the number of meetings
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(Sum([If(start_times[person] >= 0, 1, 0) for person in people]))

# Check if the problem is solvable
if objective.check() == sat:
    model = objective.model()
    itinerary = []
    for person in people:
        start = model[start_times[person]].as_long()
        end = model[end_times[person]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")