from z3 import *

# Define the locations and their travel times
locations = ["Richmond District", "The Castro", "Nob Hill", "Marina District", "Pacific Heights", 
             "Haight-Ashbury", "Mission District", "Chinatown", "Russian Hill", "Alamo Square", "Bayview"]

travel_times = {
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Bayview"): 19,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Bayview"): 27,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 20,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Bayview"): 16,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
}

# Define the people and their availability
people = {
    "Matthew": {"location": "The Castro", "start": 16.5, "end": 20.0, "min_duration": 0.75},
    "Rebecca": {"location": "Nob Hill", "start": 15.25, "end": 19.25, "min_duration": 1.75},
    "Brian": {"location": "Marina District", "start": 14.25, "end": 22.0, "min_duration": 0.5},
    "Emily": {"location": "Pacific Heights", "start": 11.25, "end": 19.75, "min_duration": 0.25},
    "Karen": {"location": "Haight-Ashbury", "start": 11.75, "end": 17.5, "min_duration": 0.5},
    "Stephanie": {"location": "Mission District", "start": 13.0, "end": 15.75, "min_duration": 1.25},
    "James": {"location": "Chinatown", "start": 14.5, "end": 19.0, "min_duration": 2.0},
    "Steven": {"location": "Russian Hill", "start": 14.0, "end": 20.0, "min_duration": 0.5},
    "Elizabeth": {"location": "Alamo Square", "start": 13.0, "end": 17.25, "min_duration": 2.0},
    "William": {"location": "Bayview", "start": 18.25, "end": 20.25, "min_duration": 1.5},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return hours * 60 + minutes

# Define the solver
solver = Solver()

# Define the variables
start_time = Int('start_time')
current_location = String('current_location')
meetings = {}

# Initial conditions
solver.add(start_time == time_to_minutes("09:00"))
solver.add(current_location == "Richmond District")

# Define the meeting variables and constraints
for person, details in people.items():
    meet_start = Int(f'meet_start_{person}')
    meet_end = Int(f'meet_end_{person}')
    meet = Bool(f'meet_{person}')
    meetings[person] = (meet, meet_start, meet_end)
    
    # Constraints for meeting
    solver.add(meet_start >= time_to_minutes("09:00"))
    solver.add(meet_end <= time_to_minutes("20:25"))
    solver.add(meet_start + details["min_duration"] * 60 <= meet_end)
    solver.add(meet_start >= details["start"] * 60)
    solver.add(meet_end <= details["end"] * 60)
    
    # Calculate travel time using If expressions
    travel_time = 0
    for loc1 in locations:
        for loc2 in locations:
            if (loc1, loc2) in travel_times:
                travel_time += If(And(current_location == loc1, details["location"] == loc2), travel_times[(loc1, loc2)], 0)
    
    solver.add(meet_start >= start_time + travel_time)
    solver.add(meet_end <= start_time + travel_time + details["min_duration"] * 60)
    
    # Update the current location and start time if meeting
    solver.add(Implies(meet, current_location == details["location"]))
    solver.add(Implies(meet, start_time == meet_end))
    
    # Ensure no overlapping meetings
    for other_person, other_details in people.items():
        if person != other_person:
            other_meet, other_meet_start, other_meet_end = meetings[other_person]
            solver.add(Or(meet_start >= other_meet_end, meet_end <= other_meet_start))

# Maximize the number of meetings
objective = Sum([If(meet, 1, 0) for meet, _, _ in meetings.values()])
solver.maximize(objective)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    result = []
    for person, (meet, meet_start, meet_end) in meetings.items():
        if model.evaluate(meet):
            start = model.evaluate(meet_start).as_long()
            end = model.evaluate(meet_end).as_long()
            result.append({
                "action": "meet",
                "person": person,
                "start_time": f"{start // 60:02}:{start % 60:02}",
                "end_time": f"{end // 60:02}:{end % 60:02}"
            })
    result = sorted(result, key=lambda x: x["start_time"])
    print({"itinerary": result})
else:
    print("No solution found")