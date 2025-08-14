from z3 import *

# Define the districts and their travel times
districts = ["Richmond District", "Sunset District", "Haight-Ashbury", "Mission District", "Golden Gate Park"]
district_indices = {district: i for i, district in enumerate(districts)}
travel_times = {
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
}

# Define the people and their availability
people = {
    "Sarah": {"district": "Sunset District", "start": 10.75, "end": 19.00, "min_meeting": 0.5},
    "Richard": {"district": "Haight-Ashbury", "start": 11.75, "end": 15.75, "min_meeting": 1.5},
    "Elizabeth": {"district": "Mission District", "start": 11.00, "end": 17.25, "min_meeting": 2.0},
    "Michelle": {"district": "Golden Gate Park", "start": 18.25, "end": 20.75, "min_meeting": 1.5},
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time * 60, 60)
    return int(hours) * 60 + int(minutes)

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_starts = {person: Int(f"{person}_start") for person in people}
meeting_ends = {person: Int(f"{person}_end") for person in people}

# Define variables for the current district at each meeting (as integers)
current_districts = {person: Int(f"{person}_district") for person in people}

# Add constraints for each person
for person, details in people.items():
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_meeting = time_to_minutes(details["min_meeting"])
    
    # Meeting must start after the person is available and end before they leave
    solver.add(meeting_starts[person] >= start_time)
    solver.add(meeting_ends[person] <= end_time)
    solver.add(meeting_ends[person] - meeting_starts[person] >= min_meeting)
    
    # Meeting must be in the person's district
    solver.add(current_districts[person] == district_indices[details["district"]])

# Add constraints for travel times
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        # If person1 meets before person2, they must travel to person2's district
        solver.add(Or(meeting_ends[person1] <= meeting_starts[person2],
                      And(current_districts[person1] == current_districts[person2],
                          meeting_ends[person1] <= meeting_starts[person2]),
                      And(current_districts[person1] != current_districts[person2],
                          meeting_ends[person1] + travel_times[(districts[current_districts[person1]], districts[current_districts[person2]])] <= meeting_starts[person2])))

# Add constraint for starting at Richmond District at 9:00AM
solver.add(meeting_starts[list(people.keys())[0]] >= time_to_minutes(9.00))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start = model[meeting_starts[person]].as_long() / 60
        end = model[meeting_ends[person]].as_long() / 60
        district_index = model[current_districts[person]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{int(start):02}:{int((start % 1) * 60):02}",
            "end_time": f"{int(end):02}:{int((end % 1) * 60):02}",
            "district": districts[district_index]
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": [{k: v for k, v in entry.items() if k != "district"} for entry in itinerary]})
else:
    print("No solution found")