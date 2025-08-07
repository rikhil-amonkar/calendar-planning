from z3 import *
from itertools import permutations

# Define the locations and their travel times
locations = ["Fisherman's Wharf", "Presidio", "Richmond District", "Financial District"]
travel_times = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21
}

# Define the friends and their availability
friends = {
    "Emily": {"location": "Presidio", "start": 16.25, "end": 21.00, "min_duration": 105/60},
    "Joseph": {"location": "Richmond District", "start": 17.25, "end": 22.00, "min_duration": 120/60},
    "Melissa": {"location": "Financial District", "start": 15.75, "end": 19.75, "min_duration": 75/60}
}

# Function to check if a given order of meetings is feasible
def is_feasible(order):
    solver = Solver()
    current_location = "Fisherman's Wharf"
    current_time = 9.00
    
    meeting_start_times = {name: Real(name + "_start") for name in order}
    meeting_end_times = {name: Real(name + "_end") for name in order}
    
    for name in order:
        start = meeting_start_times[name]
        end = meeting_end_times[name]
        details = friends[name]
        location = details["location"]
        availability_start = details["start"]
        availability_end = details["end"]
        min_duration = details["min_duration"]
        
        # Meeting must start after the current time and after the friend's availability start
        solver.add(start >= current_time)
        solver.add(start >= availability_start)
        
        # Meeting must end before the friend's availability end
        solver.add(end <= availability_end)
        
        # Meeting must last at least the minimum duration
        solver.add(end - start >= min_duration)
        
        # Travel time constraint
        travel_time = travel_times[(current_location, location)]
        solver.add(start >= current_time + travel_time / 60)
        
        # Update current time and location
        current_time = end
        current_location = location
    
    return solver.check() == sat

# Try all permutations of the friends
for order in permutations(friends.keys()):
    if is_feasible(order):
        solver = Solver()
        current_location = "Fisherman's Wharf"
        current_time = 9.00
        
        meeting_start_times = {name: Real(name + "_start") for name in order}
        meeting_end_times = {name: Real(name + "_end") for name in order}
        
        for name in order:
            start = meeting_start_times[name]
            end = meeting_end_times[name]
            details = friends[name]
            location = details["location"]
            availability_start = details["start"]
            availability_end = details["end"]
            min_duration = details["min_duration"]
            
            # Meeting must start after the current time and after the friend's availability start
            solver.add(start >= current_time)
            solver.add(start >= availability_start)
            
            # Meeting must end before the friend's availability end
            solver.add(end <= availability_end)
            
            # Meeting must last at least the minimum duration
            solver.add(end - start >= min_duration)
            
            # Travel time constraint
            travel_time = travel_times[(current_location, location)]
            solver.add(start >= current_time + travel_time / 60)
            
            # Update current time and location
            current_time = end
            current_location = location
        
        model = solver.model()
        itinerary = []
        for name in order:
            start = model[meeting_start_times[name]].as_decimal(2)
            end = model[meeting_end_times[name]].as_decimal(2)
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{int(start):02}:{int((start % 1) * 60):02}",
                "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"
            })
        print({"itinerary": itinerary})
        break
else:
    print("No solution found")