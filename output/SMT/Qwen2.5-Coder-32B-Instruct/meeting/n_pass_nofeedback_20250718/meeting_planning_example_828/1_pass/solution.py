from z3 import *

# Define the locations and their travel times
locations = ["Marina District", "Richmond District", "Union Square", "Nob Hill", "Fisherman's Wharf", 
             "Golden Gate Park", "Embarcadero", "Financial District", "North Beach", "Presidio"]

travel_times = {
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Presidio"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Presidio"): 17,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Presidio"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Presidio"): 17,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
}

# Define the people and their availability
people = {
    "Stephanie": ("Richmond District", 1635, 2130, 75),
    "William": ("Union Square", 1045, 1730, 45),
    "Elizabeth": ("Nob Hill", 1215, 1500, 105),
    "Joseph": ("Fisherman's Wharf", 1245, 1400, 75),
    "Anthony": ("Golden Gate Park", 1300, 2030, 75),
    "Barbara": ("Embarcadero", 1915, 2030, 75),
    "Carol": ("Financial District", 1145, 1615, 60),
    "Sandra": ("North Beach", 1000, 1230, 15),
    "Kenneth": ("Presidio", 2115, 2215, 45),
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables
current_location = String('current_location')
current_time = Int('current_time')
meetings = {}

# Initial conditions
solver.add(current_location == "Marina District")
solver.add(current_time == time_to_minutes(900))

# Define meeting variables and constraints
for person, (location, start, end, duration) in people.items():
    start_time = Int(f'start_time_{person}')
    end_time = Int(f'end_time_{person}')
    meetings[person] = (start_time, end_time)
    
    # Constraints for meeting times
    solver.add(start_time >= time_to_minutes(start))
    solver.add(end_time <= time_to_minutes(end))
    solver.add(end_time - start_time >= duration)
    
    # Constraints for travel time
    travel_time = Int(f'travel_time_{person}')
    solver.add(travel_time == travel_times[(current_location, location)])
    solver.add(start_time >= current_time + travel_time)
    
    # Update current location and time
    current_location = location
    current_time = end_time

# Objective: maximize the number of meetings
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(Sum([If(start_time != end_time, 1, 0) for start_time, end_time in meetings.values()]))

# Solve the problem
if objective.check() == sat:
    model = objective.model()
    itinerary = []
    for person, (start_time, end_time) in meetings.items():
        start = model.evaluate(start_time).as_long()
        end = model.evaluate(end_time).as_long()
        if start != end:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{start // 60:02}:{start % 60:02}",
                "end_time": f"{end // 60:02}:{end % 60:02}"
            })
    itinerary.sort(key=lambda x: x["start_time"])
    print(f'SOLUTION: {{"itinerary": {itinerary}}}')
else:
    print("No solution found")