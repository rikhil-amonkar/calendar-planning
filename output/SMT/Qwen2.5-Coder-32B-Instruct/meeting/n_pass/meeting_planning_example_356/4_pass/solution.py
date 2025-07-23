from z3 import *

# Define the locations and their travel times
locations = ["Bayview", "North Beach", "Presidio", "Haight-Ashbury", "Union Square"]
location_indices = {loc: i for i, loc in enumerate(locations)}
travel_times = {
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Union Square"): 17,
    ("North Beach", "Bayview"): 22,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Union Square"): 22,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18,
}

# Define the people and their availability
people = {
    "Barbara": {"location": "North Beach", "start": 13.75, "end": 20.25, "min_duration": 1.0},
    "Margaret": {"location": "Presidio", "start": 10.25, "end": 15.25, "min_duration": 0.5},
    "Kevin": {"location": "Haight-Ashbury", "start": 20.0, "end": 20.75, "min_duration": 0.5},
    "Kimberly": {"location": "Union Square", "start": 7.75, "end": 16.75, "min_duration": 0.5},
}

# Convert times to minutes for easier calculations
def time_to_minutes(time):
    hours, minutes = divmod(int(time * 100), 100)
    return hours * 60 + minutes

# Create a Z3 solver
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_start = {person: Real(f"start_{person}") for person in people}
meeting_end = {person: Real(f"end_{person}") for person in people}

# Define variables for the location at each meeting
meeting_location = {person: Int(f"location_{person}") for person in people}

# Add constraints for each person
for person, details in people.items():
    # Meeting must start after the person is available
    solver.add(meeting_start[person] >= time_to_minutes(details["start"]))
    # Meeting must end before the person is unavailable
    solver.add(meeting_end[person] <= time_to_minutes(details["end"]))
    # Meeting must last at least the minimum duration
    solver.add(meeting_end[person] - meeting_start[person] >= time_to_minutes(details["min_duration"]))
    # Meeting must be at the person's location
    solver.add(meeting_location[person] == location_indices[details["location"]])

# Define the start time at Bayview
start_time = time_to_minutes(9.0)

# Define variables for the current location and time
current_location = Int("current_location")
current_time = Real("current_time")

# Initialize the current location and time
solver.add(current_location == location_indices["Bayview"])
solver.add(current_time == start_time)

# Add constraints for traveling between meetings
people_list = list(people.keys())
for i, person1 in enumerate(people_list):
    for person2 in people_list[i+1:]:
        # If meeting with person1 ends before meeting with person2 starts
        loc1 = meeting_location[person1]
        loc2 = meeting_location[person2]
        travel_time_1_to_2 = travel_times[(locations[model.eval(loc1).as_long()], locations[model.eval(loc2).as_long()])]
        travel_time_2_to_1 = travel_times[(locations[model.eval(loc2).as_long()], locations[model.eval(loc1).as_long()])]
        solver.add(Or(meeting_end[person1] + travel_time_1_to_2 <= meeting_start[person2],
                      meeting_end[person2] + travel_time_2_to_1 <= meeting_start[person1]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start = model[meeting_start[person]].as_long() / 60.0
        end = model[meeting_end[person]].as_long() / 60.0
        loc_index = model[meeting_location[person]].as_long()
        loc_name = locations[loc_index]
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