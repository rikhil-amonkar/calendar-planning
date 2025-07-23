from z3 import *

# Define the locations and their travel times
locations = [
    "Sunset District", "Presidio", "Nob Hill", "Pacific Heights", "Mission District",
    "Marina District", "North Beach", "Russian Hill", "Richmond District", "Embarcadero",
    "Alamo Square"
]

travel_times = {
    ("Sunset District", "Presidio"): 16, ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Pacific Heights"): 21, ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Marina District"): 21, ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Russian Hill"): 24, ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Embarcadero"): 30, ("Sunset District", "Alamo Square"): 17,
    ("Presidio", "Sunset District"): 15, ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Pacific Heights"): 11, ("Presidio", "Mission District"): 26,
    ("Presidio", "Marina District"): 11, ("Presidio", "North Beach"): 18,
    ("Presidio", "Russian Hill"): 14, ("Presidio", "Richmond District"): 7,
    ("Presidio", "Embarcadero"): 20, ("Presidio", "Alamo Square"): 19,
    ("Nob Hill", "Sunset District"): 24, ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8, ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Marina District"): 11, ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Russian Hill"): 5, ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Embarcadero"): 9, ("Nob Hill", "Alamo Square"): 11,
    ("Pacific Heights", "Sunset District"): 21, ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Nob Hill"): 8, ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Marina District"): 6, ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Russian Hill"): 7, ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Embarcadero"): 10, ("Pacific Heights", "Alamo Square"): 10,
    ("Mission District", "Sunset District"): 24, ("Mission District", "Presidio"): 25,
    ("Mission District", "Nob Hill"): 12, ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Marina District"): 19, ("Mission District", "North Beach"): 17,
    ("Mission District", "Russian Hill"): 15, ("Mission District", "Richmond District"): 20,
    ("Mission District", "Embarcadero"): 19, ("Mission District", "Alamo Square"): 11,
    ("Marina District", "Sunset District"): 19, ("Marina District", "Presidio"): 10,
    ("Marina District", "Nob Hill"): 12, ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Mission District"): 20, ("Marina District", "North Beach"): 11,
    ("Marina District", "Russian Hill"): 8, ("Marina District", "Richmond District"): 11,
    ("Marina District", "Embarcadero"): 14, ("Marina District", "Alamo Square"): 15,
    ("North Beach", "Sunset District"): 27, ("North Beach", "Presidio"): 17,
    ("North Beach", "Nob Hill"): 7, ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Mission District"): 18, ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4, ("North Beach", "Richmond District"): 18,
    ("North Beach", "Embarcadero"): 6, ("North Beach", "Alamo Square"): 16,
    ("Russian Hill", "Sunset District"): 23, ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Nob Hill"): 5, ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Mission District"): 16, ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5, ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Embarcadero"): 8, ("Russian Hill", "Alamo Square"): 15,
    ("Richmond District", "Sunset District"): 11, ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Nob Hill"): 17, ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Mission District"): 20, ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17, ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Embarcadero"): 19, ("Richmond District", "Alamo Square"): 13,
    ("Embarcadero", "Sunset District"): 30, ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Nob Hill"): 10, ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Mission District"): 20, ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "North Beach"): 5, ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Richmond District"): 21, ("Embarcadero", "Alamo Square"): 19,
    ("Alamo Square", "Sunset District"): 16, ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Nob Hill"): 11, ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Mission District"): 10, ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "North Beach"): 15, ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Richmond District"): 11, ("Alamo Square", "Embarcadero"): 16,
}

# Define the people and their availability
people = {
    "Charles": {"location": "Presidio", "start": 13.25, "end": 15.00, "min_duration": 105},
    "Robert": {"location": "Nob Hill", "start": 13.25, "end": 17.50, "min_duration": 90},
    "Nancy": {"location": "Pacific Heights", "start": 14.75, "end": 22.00, "min_duration": 105},
    "Brian": {"location": "Mission District", "start": 15.50, "end": 22.00, "min_duration": 60},
    "Kimberly": {"location": "Marina District", "start": 17.00, "end": 19.75, "min_duration": 75},
    "David": {"location": "North Beach", "start": 14.75, "end": 16.50, "min_duration": 75},
    "William": {"location": "Russian Hill", "start": 12.50, "end": 19.25, "min_duration": 120},
    "Jeffrey": {"location": "Richmond District", "start": 12.00, "end": 19.25, "min_duration": 45},
    "Karen": {"location": "Embarcadero", "start": 14.25, "end": 20.75, "min_duration": 60},
    "Joshua": {"location": "Alamo Square", "start": 18.75, "end": 22.00, "min_duration": 60},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time * 60, 60)
    return int(hours * 60 + minutes)

# Create the solver
solver = Solver()

# Define the variables
current_location = "Sunset District"
current_time = 9 * 60  # 9:00 AM in minutes
meetings = []

# Define the meeting variables
meeting_vars = {person: Bool(f"meet_{person}") for person in people}

# Define the start and end times for each meeting
start_times = {person: Int(f"start_{person}") for person in people}
end_times = {person: Int(f"end_{person}") for person in people}

# Add constraints for each person
for person, details in people.items():
    location = details["location"]
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    min_duration = details["min_duration"]

    # Meeting must start after the current time and before the person's availability ends
    solver.add(start_times[person] >= current_time)
    solver.add(start_times[person] <= end - min_duration)

    # Meeting must end before the person's availability ends
    solver.add(end_times[person] <= end)

    # Meeting must last at least the minimum duration
    solver.add(end_times[person] - start_times[person] >= min_duration)

    # If meeting with this person, start and end times must be set
    solver.add(Implies(meeting_vars[person], And(start_times[person] >= start, end_times[person] <= end)))

    # If not meeting with this person, start and end times must be 0
    solver.add(Implies(Not(meeting_vars[person]), And(start_times[person] == 0, end_times[person] == 0)))

    # Update the current time and location if meeting with this person
    solver.add(Implies(meeting_vars[person], current_time == end_times[person] + travel_times[(current_location, location)]))
    current_location = location

# Maximize the number of meetings
solver.maximize(Sum([If(meeting_vars[person], 1, 0) for person in people]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        if model.evaluate(meeting_vars[person]):
            start = model.evaluate(start_times[person]).as_long() // 60
            end = model.evaluate(end_times[person]).as_long() // 60
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{start:02}:{model.evaluate(start_times[person]).as_long() % 60:02}",
                "end_time": f"{end:02}:{model.evaluate(end_times[person]).as_long() % 60:02}"
            })
    print({"itinerary": itinerary})
else:
    print("No solution found")