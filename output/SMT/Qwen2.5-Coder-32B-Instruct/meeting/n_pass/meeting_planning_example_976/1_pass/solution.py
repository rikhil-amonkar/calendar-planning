from z3 import *

# Define the locations and their travel times
locations = ["Embarcadero", "Bayview", "Chinatown", "Alamo Square", "Nob Hill", "Presidio", "Union Square", "The Castro", "North Beach", "Fisherman's Wharf", "Marina District"]
travel_times = {
    "Embarcadero": {"Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20, "Union Square": 10, "The Castro": 25, "North Beach": 5, "Fisherman's Wharf": 6, "Marina District": 12},
    "Bayview": {"Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20, "Presidio": 32, "Union Square": 18, "The Castro": 19, "North Beach": 22, "Fisherman's Wharf": 25, "Marina District": 27},
    "Chinatown": {"Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9, "Presidio": 19, "Union Square": 7, "The Castro": 22, "North Beach": 3, "Fisherman's Wharf": 8, "Marina District": 12},
    "Alamo Square": {"Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11, "Presidio": 17, "Union Square": 14, "The Castro": 8, "North Beach": 15, "Fisherman's Wharf": 19, "Marina District": 15},
    "Nob Hill": {"Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11, "Presidio": 17, "Union Square": 7, "The Castro": 17, "North Beach": 8, "Fisherman's Wharf": 10, "Marina District": 11},
    "Presidio": {"Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19, "Nob Hill": 18, "Union Square": 22, "The Castro": 21, "North Beach": 17, "Fisherman's Wharf": 17, "Marina District": 11},
    "Union Square": {"Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15, "Nob Hill": 9, "Presidio": 24, "The Castro": 17, "North Beach": 7, "Fisherman's Wharf": 13, "Marina District": 16},
    "The Castro": {"Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8, "Nob Hill": 16, "Presidio": 20, "Union Square": 19, "North Beach": 20, "Fisherman's Wharf": 27, "Marina District": 21},
    "North Beach": {"Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16, "Nob Hill": 7, "Presidio": 17, "Union Square": 7, "The Castro": 23, "Fisherman's Wharf": 5, "Marina District": 9},
    "Fisherman's Wharf": {"Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Union Square": 13, "The Castro": 27, "North Beach": 6, "Marina District": 9},
    "Marina District": {"Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15, "Nob Hill": 12, "Presidio": 10, "Union Square": 16, "The Castro": 22, "North Beach": 11, "Fisherman's Wharf": 10}
}

# Define the people and their availability
people = {
    "Matthew": {"location": "Bayview", "start": 19.25, "end": 22.00, "duration": 120},
    "Karen": {"location": "Chinatown", "start": 19.25, "end": 19.75, "duration": 90},
    "Sarah": {"location": "Alamo Square", "start": 20.00, "end": 21.75, "duration": 105},
    "Jessica": {"location": "Nob Hill", "start": 16.50, "end": 18.75, "duration": 120},
    "Stephanie": {"location": "Presidio", "start": 7.50, "end": 10.25, "duration": 60},
    "Mary": {"location": "Union Square", "start": 16.75, "end": 21.50, "duration": 60},
    "Charles": {"location": "The Castro", "start": 16.50, "end": 22.00, "duration": 105},
    "Nancy": {"location": "North Beach", "start": 14.75, "end": 20.00, "duration": 15},
    "Thomas": {"location": "Fisherman's Wharf", "start": 13.50, "end": 19.00, "duration": 30},
    "Brian": {"location": "Marina District", "start": 12.25, "end": 18.00, "duration": 60}
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return hours * 60 + minutes

# Create a Z3 solver
solver = Solver()

# Define variables for each meeting
meetings = {}
for person, details in people.items():
    start = Real(f'start_{person}')
    end = Real(f'end_{person}')
    meetings[person] = (start, end)
    solver.add(start >= time_to_minutes("09:00"))
    solver.add(end <= time_to_minutes("22:00"))
    solver.add(end - start >= details["duration"])
    solver.add(start >= details["start"] * 60)
    solver.add(end <= details["end"] * 60)

# Define travel constraints
current_location = "Embarcadero"
current_time = time_to_minutes("09:00")
for person, (start, end) in meetings.items():
    location = people[person]["location"]
    travel_time = travel_times[current_location][location]
    solver.add(start >= current_time + travel_time)
    current_location = location
    current_time = end

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, (start, end) in meetings.items():
        start_time = model[start].as_long() // 60
        start_minutes = model[start].as_long() % 60
        end_time = model[end].as_long() // 60
        end_minutes = model[end].as_long() % 60
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start_time:02}:{start_minutes:02}",
            "end_time": f"{end_time:02}:{end_minutes:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")