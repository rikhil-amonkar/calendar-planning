from z3 import *

# Define the locations and their travel times
locations = ["Marina District", "Embarcadero", "Bayview", "Union Square", "Chinatown", 
             "Sunset District", "Golden Gate Park", "Financial District", "Haight-Ashbury", "Mission District"]

travel_times = {
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 25,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
}

# Define the people and their availability
people = {
    "Joshua": {"location": "Embarcadero", "start": 9*60 + 45, "end": 18*60, "min_duration": 105},
    "Jeffrey": {"location": "Bayview", "start": 9*60 + 45, "end": 20*60 + 15, "min_duration": 75},
    "Charles": {"location": "Union Square", "start": 10*60 + 45, "end": 20*60 + 15, "min_duration": 120},
    "Joseph": {"location": "Chinatown", "start": 7*60, "end": 15*60 + 30, "min_duration": 60},
    "Elizabeth": {"location": "Sunset District", "start": 9*60, "end": 9*60 + 45, "min_duration": 45},
    "Matthew": {"location": "Golden Gate Park", "start": 11*60, "end": 19*60 + 30, "min_duration": 45},
    "Carol": {"location": "Financial District", "start": 10*60 + 45, "end": 11*60 + 15, "min_duration": 15},
    "Paul": {"location": "Haight-Ashbury", "start": 19*60 + 15, "end": 20*60 + 30, "min_duration": 15},
    "Rebecca": {"location": "Mission District", "start": 17*60, "end": 21*60 + 45, "min_duration": 45},
}

# Create an optimizer instance
optimizer = Optimize()

# Define variables
start_time = Int('start_time')
current_location = String('current_location')
meetings = {person: Bool(f'meet_{person}') for person in people}
meeting_start_times = {person: Int(f'start_{person}') for person in people}
meeting_end_times = {person: Int(f'end_{person}') for person in people}

# Initial conditions
optimizer.add(start_time == 9*60)
optimizer.add(current_location == "Marina District")

# Constraints for each person
for person, details in people.items():
    loc = details["location"]
    start = details["start"]
    end = details["end"]
    min_duration = details["min_duration"]
    
    # If meeting with person, start and end times must be within their availability
    optimizer.add(Implies(meetings[person], meeting_start_times[person] >= start))
    optimizer.add(Implies(meetings[person], meeting_end_times[person] <= end))
    optimizer.add(Implies(meetings[person], meeting_end_times[person] - meeting_start_times[person] >= min_duration))
    
    # Travel time constraints
    travel_time = travel_times.get((current_location.as_string(), loc), 1000)  # Default to a large number if not found
    optimizer.add(Implies(meetings[person], meeting_start_times[person] >= start_time + travel_time))
    optimizer.add(Implies(meetings[person], meeting_end_times[person] <= end - min_duration))
    
    # Update start_time and current_location after meeting
    optimizer.add(Implies(meetings[person], start_time == meeting_end_times[person]))
    optimizer.add(Implies(meetings[person], current_location == loc))

# Objective: maximize the number of meetings
objective = Sum([If(meetings[person], 1, 0) for person in people])
optimizer.maximize(objective)

# Check if the problem is solvable
if optimizer.check() == sat:
    model = optimizer.model()
    itinerary = []
    for person in people:
        if model.evaluate(meetings[person]):
            start = model.evaluate(meeting_start_times[person]).as_long()
            end = model.evaluate(meeting_end_times[person]).as_long()
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{start//60:02}:{start%60:02}",
                "end_time": f"{end//60:02}:{end%60:02}"
            })
    print({"itinerary": itinerary})
else:
    print("No solution found")