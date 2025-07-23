from z3 import *

# Define the locations and their travel times
locations = ["Presidio", "Golden Gate Park", "Bayview", "Chinatown", "North Beach", "Mission District"]
travel_times = {
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Mission District"): 26,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Mission District"): 13,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Mission District"): 18,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Mission District"): 18,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "North Beach"): 17,
}

# Define the people and their availability
people = {
    "Jessica": {"location": "Golden Gate Park", "start": 13.75, "end": 15.0, "min_duration": 0.5},
    "Ashley": {"location": "Bayview", "start": 17.25, "end": 20.0, "min_duration": 1.75},
    "Ronald": {"location": "Chinatown", "start": 7.25, "end": 14.75, "min_duration": 1.5},
    "William": {"location": "North Beach", "start": 13.25, "end": 20.25, "min_duration": 0.25},
    "Daniel": {"location": "Mission District", "start": 7.0, "end": 11.25, "min_duration": 1.75},
}

# Convert times to minutes for easier calculations
def time_to_minutes(time):
    hours, minutes = divmod(time * 60, 60)
    return int(hours) * 60 + int(minutes)

# Create a Z3 solver
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {person: Int(f"{person}_start") for person in people}
meeting_end = {person: Int(f"{person}_end") for person in people}

# Define the start time at Presidio
start_time = time_to_minutes(9.0)

# Add constraints for each person
for person, details in people.items():
    loc = details["location"]
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    min_duration = time_to_minutes(details["min_duration"])
    
    # Meeting must start after arrival and before the person leaves
    solver.add(meeting_start[person] >= start_time)
    solver.add(meeting_start[person] + min_duration <= end)
    
    # Meeting must end before the person leaves
    solver.add(meeting_end[person] <= end)
    
    # Meeting must be at least the minimum duration
    solver.add(meeting_end[person] - meeting_start[person] >= min_duration)

# Add constraints for travel times
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        loc1 = people[person1]["location"]
        loc2 = people[person2]["location"]
        travel_time = travel_times[(loc1, loc2)]
        
        # If meeting with person1 ends before meeting with person2 starts, add travel time constraint
        solver.add(Or(meeting_end[person1] + travel_time <= meeting_start[person2],
                      meeting_end[person2] + travel_time <= meeting_start[person1]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start = model[meeting_start[person]].as_long() / 60
        end = model[meeting_end[person]].as_long() / 60
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{int(start):02}:{int((start % 1) * 60):02}",
            "end_time": f"{int(end):02}:{int((end % 1) * 60):02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")