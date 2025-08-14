from z3 import *

# Define the locations
locations = ["Bayview", "North Beach", "Presidio", "Haight-Ashbury", "Union Square"]

# Define the travel times in minutes
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
people_availability = {
    "Barbara": ("North Beach", 13.75, 20.25, 60),  # 1:45PM to 8:15PM, 60 minutes
    "Margaret": ("Presidio", 10.25, 15.25, 30),  # 10:15AM to 3:15PM, 30 minutes
    "Kevin": ("Haight-Ashbury", 20.0, 20.75, 30),  # 8:00PM to 8:45PM, 30 minutes
    "Kimberly": ("Union Square", 7.75, 16.75, 30),  # 7:45AM to 4:45PM, 30 minutes
}

# Create a solver
solver = Solver()

# Define the start time for each person's meeting
start_times = {person: Real(f"start_{person}") for person in people_availability}

# Define the location for each person's meeting
location_vars = {person: String(f"location_{person}") for person in people_availability}

# Define the current location and time
current_location = "Bayview"
current_time = 9.0  # 9:00AM

# Add constraints for each person
for person, (location, start, end, duration) in people_availability.items():
    # Meeting must start within the person's availability
    solver.add(start_times[person] >= start)
    solver.add(start_times[person] <= end - duration / 60)
    # Meeting must end within the person's availability
    solver.add(start_times[person] + duration / 60 <= end)
    # Meeting must be at the correct location
    solver.add(location_vars[person] == location)

# Check if the initial constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Add constraints for travel times
    for i, person1 in enumerate(people_availability):
        for person2 in list(people_availability.keys())[i+1:]:
            # If person1 meets before person2, the travel time must be considered
            loc1 = model[location_vars[person1]].as_string()[1:-1]  # Remove quotes
            loc2 = model[location_vars[person2]].as_string()[1:-1]  # Remove quotes
            travel_time_expr = If(start_times[person1] < start_times[person2],
                                  travel_times[(loc1, loc2)],
                                  travel_times[(loc2, loc1)])
            solver.add(start_times[person1] + people_availability[person1][3] / 60 + travel_time_expr / 60 <= start_times[person2])

    # Check again after adding travel time constraints
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for person, (location, start, end, duration) in people_availability.items():
            start_time = model[start_times[person]].as_decimal(2)
            end_time = start_time + duration / 60
            itinerary.append({"action": "meet", "person": person, "start_time": f"{int(start_time):02}:{int((start_time % 1) * 60):02}", "end_time": f"{int(end_time):02}:{int((end_time % 1) * 60):02}"})
        itinerary.sort(key=lambda x: x["start_time"])
        print({"itinerary": itinerary})
    else:
        print("No solution found after adding travel time constraints")
else:
    print("No solution found")