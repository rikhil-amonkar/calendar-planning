from z3 import *

# Define the locations
locations = ["Alamo Square", "Russian Hill", "Presidio", "Chinatown", "Sunset District", "The Castro", "Embarcadero", "Golden Gate Park"]

# Define the travel times using indices
travel_times = {
    (0, 1): 13,  # Alamo Square to Russian Hill
    (0, 2): 18,  # Alamo Square to Presidio
    (0, 3): 16,  # Alamo Square to Chinatown
    (0, 4): 16,  # Alamo Square to Sunset District
    (0, 5): 8,   # Alamo Square to The Castro
    (0, 6): 17,  # Alamo Square to Embarcadero
    (0, 7): 9,   # Alamo Square to Golden Gate Park
    (1, 0): 15,  # Russian Hill to Alamo Square
    (1, 2): 14,  # Russian Hill to Presidio
    (1, 3): 9,   # Russian Hill to Chinatown
    (1, 4): 23,  # Russian Hill to Sunset District
    (1, 5): 21,  # Russian Hill to The Castro
    (1, 6): 8,   # Russian Hill to Embarcadero
    (1, 7): 21,  # Russian Hill to Golden Gate Park
    (2, 0): 18,  # Presidio to Alamo Square
    (2, 1): 14,  # Presidio to Russian Hill
    (2, 3): 21,  # Presidio to Chinatown
    (2, 4): 15,  # Presidio to Sunset District
    (2, 5): 21,  # Presidio to The Castro
    (2, 6): 20,  # Presidio to Embarcadero
    (2, 7): 12,  # Presidio to Golden Gate Park
    (3, 0): 17,  # Chinatown to Alamo Square
    (3, 1): 7,   # Chinatown to Russian Hill
    (3, 2): 19,  # Chinatown to Presidio
    (3, 4): 29,  # Chinatown to Sunset District
    (3, 5): 22,  # Chinatown to The Castro
    (3, 6): 5,   # Chinatown to Embarcadero
    (3, 7): 23,  # Chinatown to Golden Gate Park
    (4, 0): 17,  # Sunset District to Alamo Square
    (4, 1): 24,  # Sunset District to Russian Hill
    (4, 2): 16,  # Sunset District to Presidio
    (4, 3): 30,  # Sunset District to Chinatown
    (4, 5): 17,  # Sunset District to The Castro
    (4, 6): 31,  # Sunset District to Embarcadero
    (4, 7): 11,  # Sunset District to Golden Gate Park
    (5, 0): 8,   # The Castro to Alamo Square
    (5, 1): 18,  # The Castro to Russian Hill
    (5, 2): 20,  # The Castro to Presidio
    (5, 3): 20,  # The Castro to Chinatown
    (5, 4): 17,  # The Castro to Sunset District
    (5, 6): 22,  # The Castro to Embarcadero
    (5, 7): 11,  # The Castro to Golden Gate Park
    (6, 0): 19,  # Embarcadero to Alamo Square
    (6, 1): 8,   # Embarcadero to Russian Hill
    (6, 2): 20,  # Embarcadero to Presidio
    (6, 3): 7,   # Embarcadero to Chinatown
    (6, 4): 30,  # Embarcadero to Sunset District
    (6, 5): 25,  # Embarcadero to The Castro
    (6, 7): 25,  # Embarcadero to Golden Gate Park
    (7, 0): 10,  # Golden Gate Park to Alamo Square
    (7, 1): 19,  # Golden Gate Park to Russian Hill
    (7, 2): 11,  # Golden Gate Park to Presidio
    (7, 3): 23,  # Golden Gate Park to Chinatown
    (7, 4): 10,  # Golden Gate Park to Sunset District
    (7, 5): 13,  # Golden Gate Park to The Castro
    (7, 6): 25,  # Golden Gate Park to Embarcadero
}

# Define the friends and their availability
friends = {
    "Emily": {"location": 1, "start": 12*60 + 15, "end": 14*60 + 15, "min_duration": 105},
    "Mark": {"location": 2, "start": 14*60 + 45, "end": 19*60 + 30, "min_duration": 60},
    "Deborah": {"location": 3, "start": 7*60 + 30, "end": 15*60 + 30, "min_duration": 45},
    "Margaret": {"location": 4, "start": 21*60 + 30, "end": 22*60 + 30, "min_duration": 60},
    "George": {"location": 5, "start": 7*60 + 30, "end": 14*60 + 15, "min_duration": 60},
    "Andrew": {"location": 6, "start": 20*60 + 15, "end": 22*60, "min_duration": 75},
    "Steven": {"location": 7, "start": 11*60 + 15, "end": 21*60 + 15, "min_duration": 105},
}

# Create a solver
solver = Solver()

# Define the variables
current_location = Int("current_location")
current_time = Int("current_time")
meetings = {}

# Initialize the current location and time
solver.add(current_location == 0)  # Alamo Square
solver.add(current_time == 9*60)

# Define the meeting variables and constraints
for friend, details in friends.items():
    start_time = Int(f"{friend}_start_time")
    end_time = Int(f"{friend}_end_time")
    meetings[friend] = (start_time, end_time)
    
    # Constraints for meeting times
    solver.add(start_time >= details["start"])
    solver.add(end_time <= details["end"])
    solver.add(end_time - start_time >= details["min_duration"])
    
    # Constraints for travel time
    travel_time = Int(f"travel_time_to_{friend}")
    travel_time_expr = 0
    for (loc1, loc2), time in travel_times.items():
        travel_time_expr = If(And(current_location == loc1, details["location"] == loc2), time, travel_time_expr)
    solver.add(travel_time == travel_time_expr)
    solver.add(start_time >= current_time + travel_time)
    
    # Update current location and time
    current_location = details["location"]
    current_time = end_time

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend, (start_var, end_var) in meetings.items():
        start_time = model[start_var].as_long()
        end_time = model[end_var].as_long()
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": f"{start_time // 60:02}:{start_time % 60:02}",
            "end_time": f"{end_time // 60:02}:{end_time % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")