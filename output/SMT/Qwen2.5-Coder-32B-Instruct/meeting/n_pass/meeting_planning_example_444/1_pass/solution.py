from z3 import *

# Define the locations and their travel times
locations = ["Financial District", "Russian Hill", "Sunset District", "North Beach", "The Castro", "Golden Gate Park"]
travel_times = {
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,
    ("The Castro", "Financial District"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13,
}

# Define the people and their availability
people = {
    "Ronald": {"location": "Russian Hill", "start": 13.75, "end": 17.25, "min_duration": 105/60},
    "Patricia": {"location": "Sunset District", "start": 9.25, "end": 22.0, "min_duration": 60/60},
    "Laura": {"location": "North Beach", "start": 12.5, "end": 12.75, "min_duration": 15/60},
    "Emily": {"location": "The Castro", "start": 16.25, "end": 18.5, "min_duration": 60/60},
    "Mary": {"location": "Golden Gate Park", "start": 15.0, "end": 16.5, "min_duration": 60/60},
}

# Convert times to minutes for easier calculations
def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return hours * 60 + minutes

# Define the solver
solver = Solver()

# Define the variables
start_times = {person: Real(f'start_{person}') for person in people}
end_times = {person: Real(f'end_{person}') for person in people}
current_location = String('current_location')
current_time = Real('current_time')

# Initial conditions
solver.add(current_location == "Financial District")
solver.add(current_time == time_to_minutes("09:00"))

# Constraints for each person
for person, details in people.items():
    location = details["location"]
    start = details["start"] * 60  # Convert to minutes
    end = details["end"] * 60  # Convert to minutes
    min_duration = details["min_duration"] * 60  # Convert to minutes

    # Meeting must start and end within the person's availability
    solver.add(start_times[person] >= start)
    solver.add(end_times[person] <= end)
    solver.add(end_times[person] - start_times[person] >= min_duration)

    # Travel constraints
    travel_time = travel_times[(current_location, location)]
    solver.add(start_times[person] >= current_time + travel_time)

    # Update current location and time after meeting
    current_location = location
    current_time = end_times[person]

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start = model[start_times[person]].as_long() // 60
        end = model[end_times[person]].as_long() // 60
        start_time = f"{start:02}:{model[start_times[person]].as_long() % 60:02}"
        end_time = f"{end:02}:{model[end_times[person]].as_long() % 60:02}"
        itinerary.append({"action": "meet", "person": person, "start_time": start_time, "end_time": end_time})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")