from z3 import *
from itertools import permutations

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
    "Ronald": {"location": "Russian Hill", "start": 13.75, "end": 17.25, "min_duration": 105},
    "Patricia": {"location": "Sunset District", "start": 9.25, "end": 22.0, "min_duration": 60},
    "Laura": {"location": "North Beach", "start": 12.5, "end": 12.75, "min_duration": 15},
    "Emily": {"location": "The Castro", "start": 16.25, "end": 18.5, "min_duration": 60},
    "Mary": {"location": "Golden Gate Park", "start": 15.0, "end": 16.5, "min_duration": 60},
}

# Convert times to minutes for easier calculations
def time_to_minutes(time):
    hours, minutes = divmod(time * 60, 60)
    return int(hours) * 60 + int(minutes)

# Function to check if a given order of meetings is feasible
def check_order(order):
    solver = Solver()
    meeting_vars = {}
    current_location = "Financial District"
    current_time = time_to_minutes(9.0)
    
    for person in order:
        details = people[person]
        start = Int(f"{person}_start")
        end = Int(f"{person}_end")
        meeting_vars[person] = (start, end)
        solver.add(start >= time_to_minutes(details["start"]))
        solver.add(end <= time_to_minutes(details["end"]))
        solver.add(end - start >= details["min_duration"])
        travel_time = travel_times[(current_location, details["location"])]
        solver.add(start >= current_time + travel_time)
        current_location = details["location"]
        current_time = end
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for person, (start, end) in meeting_vars.items():
            start_time = model.evaluate(start).as_long()
            end_time = model.evaluate(end).as_long()
            if start_time != end_time:
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
                    "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
                })
        itinerary.sort(key=lambda x: x["start_time"])
        return itinerary
    return None

# Try all permutations of the people
people_list = list(people.keys())
for order in permutations(people_list):
    itinerary = check_order(order)
    if itinerary:
        print({"itinerary": itinerary})
        break
else:
    print("No solution found")