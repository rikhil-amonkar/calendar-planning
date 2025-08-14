from z3 import *

# Define the locations and their travel times
locations = ["Sunset District", "Russian Hill", "Chinatown", "Presidio", "Fisherman's Wharf"]
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Presidio"): 17,
}

# Define the people and their availability
people = {
    "William": {"location": "Russian Hill", "start": 18.5, "end": 20.75, "min_meeting": 105},
    "Michelle": {"location": "Chinatown", "start": 8.25, "end": 14.0, "min_meeting": 15},
    "George": {"location": "Presidio", "start": 10.5, "end": 18.75, "min_meeting": 30},
    "Robert": {"location": "Fisherman's Wharf", "start": 9.0, "end": 13.75, "min_meeting": 30},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return hours * 60 + minutes

# Define the solver
solver = Solver()

# Define the variables
current_location = String('current_location')
current_time = Real('current_time')
meetings = {person: Bool(f'meet_{person}') for person in people}

# Initial conditions
solver.add(current_location == "Sunset District")
solver.add(current_time == time_to_minutes("09:00"))

# Define the constraints for each person
for person, details in people.items():
    location = details["location"]
    start_time = time_to_minutes(f"{int(details['start']):02}:{int((details['start'] % 1) * 60):02}")
    end_time = time_to_minutes(f"{int(details['end']):02}:{int((details['end'] % 1) * 60):02}")
    min_meeting = details["min_meeting"]
    
    # If meeting with this person, we need to be at their location within their availability
    meeting_start = Real(f'meeting_start_{person}')
    meeting_end = Real(f'meeting_end_{person}')
    
    solver.add(Implies(meetings[person], current_location == location))
    solver.add(Implies(meetings[person], meeting_start >= current_time))
    solver.add(Implies(meetings[person], meeting_start >= start_time))
    solver.add(Implies(meetings[person], meeting_end <= end_time))
    solver.add(Implies(meetings[person], meeting_end - meeting_start >= min_meeting))
    solver.add(Implies(meetings[person], current_time == meeting_end))
    
    # If not meeting with this person, we just move to the next location
    solver.add(Implies(Not(meetings[person]), current_time + travel_times[(current_location, location)] <= end_time))

# Define the objective: maximize the number of meetings
objective = Sum([If(meetings[person], 1, 0) for person in people])
solver.maximize(objective)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, details in people.items():
        if model.evaluate(meetings[person]):
            meeting_start = model.evaluate(Real(f'meeting_start_{person}')).as_long()
            meeting_end = model.evaluate(Real(f'meeting_end_{person}')).as_long()
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{meeting_start // 60:02}:{meeting_start % 60:02}",
                "end_time": f"{meeting_end // 60:02}:{meeting_end % 60:02}"
            })
    print({"itinerary": itinerary})
else:
    print("No solution found")