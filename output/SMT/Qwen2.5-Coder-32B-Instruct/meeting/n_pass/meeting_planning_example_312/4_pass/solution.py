from z3 import *

# Define the districts and their travel times
districts = ["Richmond District", "Sunset District", "Haight-Ashbury", "Mission District", "Golden Gate Park"]
district_to_index = {district: i for i, district in enumerate(districts)}
travel_times = {
    (0, 1): 11,  # Richmond District to Sunset District
    (0, 2): 10,  # Richmond District to Haight-Ashbury
    (0, 3): 20,  # Richmond District to Mission District
    (0, 4): 9,   # Richmond District to Golden Gate Park
    (1, 0): 12,  # Sunset District to Richmond District
    (1, 2): 15,  # Sunset District to Haight-Ashbury
    (1, 3): 24,  # Sunset District to Mission District
    (1, 4): 11,  # Sunset District to Golden Gate Park
    (2, 0): 10,  # Haight-Ashbury to Richmond District
    (2, 1): 15,  # Haight-Ashbury to Sunset District
    (2, 3): 11,  # Haight-Ashbury to Mission District
    (2, 4): 7,   # Haight-Ashbury to Golden Gate Park
    (3, 0): 20,  # Mission District to Richmond District
    (3, 1): 24,  # Mission District to Sunset District
    (3, 2): 12,  # Mission District to Haight-Ashbury
    (3, 4): 17,  # Mission District to Golden Gate Park
    (4, 0): 7,   # Golden Gate Park to Richmond District
    (4, 1): 10,  # Golden Gate Park to Sunset District
    (4, 2): 7,   # Golden Gate Park to Haight-Ashbury
    (4, 3): 17,  # Golden Gate Park to Mission District
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

# Define variables for the current district at each meeting
current_districts = {person: Int(f"{person}_district") for person in people}

# Add constraints for each person's meeting
for person, details in people.items():
    start_time = time_to_minutes(details["start"])
    end_time = time_to_minutes(details["end"])
    min_meeting = int(details["min_meeting"] * 60)
    
    # Meeting must start and end within the person's availability
    solver.add(meeting_starts[person] >= start_time)
    solver.add(meeting_ends[person] <= end_time)
    solver.add(meeting_ends[person] - meeting_starts[person] >= min_meeting)
    
    # Meeting must be in the person's district
    solver.add(current_districts[person] == district_to_index[details["district"]])

# Add constraints for travel times
for i, person1 in enumerate(people):
    for person2 in list(people.keys())[i+1:]:
        # If person1's meeting ends before person2's meeting starts, they can travel
        for (d1, d2), travel_time in travel_times.items():
            solver.add(Or(meeting_ends[person1] + travel_time <= meeting_starts[person2],
                          meeting_ends[person2] + travel_time <= meeting_starts[person1],
                          current_districts[person1] != d1,
                          current_districts[person2] != d2))

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
        district = districts[district_index]
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