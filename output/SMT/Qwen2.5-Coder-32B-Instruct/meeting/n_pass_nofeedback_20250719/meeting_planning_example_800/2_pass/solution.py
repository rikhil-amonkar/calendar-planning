from z3 import *

# Define the locations and their travel times
locations = ["Union Square", "The Castro", "North Beach", "Embarcadero", "Alamo Square", "Nob Hill", "Presidio", "Fisherman's Wharf", "Mission District", "Haight-Ashbury"]
travel_times = {
    "Union Square": {"Union Square": 0, "The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15, "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14, "Haight-Ashbury": 18},
    "The Castro": {"Union Square": 19, "The Castro": 0, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8, "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7, "Haight-Ashbury": 6},
    "North Beach": {"Union Square": 7, "The Castro": 23, "North Beach": 0, "Embarcadero": 6, "Alamo Square": 16, "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Mission District": 18, "Haight-Ashbury": 18},
    "Embarcadero": {"Union Square": 10, "The Castro": 25, "North Beach": 5, "Embarcadero": 0, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20, "Fisherman's Wharf": 6, "Mission District": 20, "Haight-Ashbury": 21},
    "Alamo Square": {"Union Square": 14, "The Castro": 8, "North Beach": 15, "Embarcadero": 16, "Alamo Square": 0, "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 19, "Mission District": 10, "Haight-Ashbury": 5},
    "Nob Hill": {"Union Square": 7, "The Castro": 17, "North Beach": 8, "Embarcadero": 9, "Alamo Square": 11, "Nob Hill": 0, "Presidio": 17, "Fisherman's Wharf": 10, "Mission District": 13, "Haight-Ashbury": 13},
    "Presidio": {"Union Square": 22, "The Castro": 21, "North Beach": 18, "Embarcadero": 20, "Alamo Square": 19, "Nob Hill": 18, "Presidio": 0, "Fisherman's Wharf": 19, "Mission District": 26, "Haight-Ashbury": 15},
    "Fisherman's Wharf": {"Union Square": 13, "The Castro": 27, "North Beach": 6, "Embarcadero": 8, "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 0, "Mission District": 22, "Haight-Ashbury": 22},
    "Mission District": {"Union Square": 15, "The Castro": 7, "North Beach": 17, "Embarcadero": 19, "Alamo Square": 11, "Nob Hill": 12, "Presidio": 25, "Fisherman's Wharf": 22, "Mission District": 0, "Haight-Ashbury": 12},
    "Haight-Ashbury": {"Union Square": 19, "The Castro": 6, "North Beach": 19, "Embarcadero": 20, "Alamo Square": 5, "Nob Hill": 15, "Presidio": 15, "Fisherman's Wharf": 23, "Mission District": 11, "Haight-Ashbury": 0}
}

# Define the people and their availability
people = {
    "Melissa": {"location": "The Castro", "start": 2015, "end": 2115, "min_duration": 30},
    "Kimberly": {"location": "North Beach", "start": 700, "end": 1030, "min_duration": 15},
    "Joseph": {"location": "Embarcadero", "start": 1530, "end": 1930, "min_duration": 75},
    "Barbara": {"location": "Alamo Square", "start": 2045, "end": 2145, "min_duration": 15},
    "Kenneth": {"location": "Nob Hill", "start": 1215, "end": 1715, "min_duration": 105},
    "Joshua": {"location": "Presidio", "start": 1630, "end": 1815, "min_duration": 105},
    "Brian": {"location": "Fisherman's Wharf", "start": 930, "end": 1530, "min_duration": 45},
    "Steven": {"location": "Mission District", "start": 1930, "end": 2100, "min_duration": 90},
    "Betty": {"location": "Haight-Ashbury", "start": 1900, "end": 2030, "min_duration": 90}
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a Z3 solver
solver = Solver()

# Define a time slot for each minute from 9:00 AM to 10:00 PM (13:00 to 22:00 in 24-hour format)
time_slots = list(range(time_to_minutes(900), time_to_minutes(2200) + 1))

# Define binary variables for each person and time slot
meeting_vars = {}
for person, details in people.items():
    meeting_vars[person] = [Bool(f"{person}_at_{time}") for time in time_slots]

# Define constraints for each person
for person, details in people.items():
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    min_duration = details["min_duration"]
    location = details["location"]
    
    # Ensure the person is available within their time window
    for time in time_slots:
        if time < start or time > end:
            solver.add(Not(meeting_vars[person][time - time_slots[0]]))
    
    # Ensure the person is available for at least the minimum duration
    for i in range(len(time_slots) - min_duration + 1):
        solver.add(Or([And(meeting_vars[person][j] for j in range(i, i + min_duration))]))
    
    # Ensure the person is not meeting at two different times
    for i in range(len(time_slots) - 1):
        solver.add(Implies(meeting_vars[person][i], Not(meeting_vars[person][i + 1])))

# Define constraints for travel times
for i in range(len(time_slots) - 1):
    for person1, details1 in people.items():
        for person2, details2 in people.items():
            if person1 != person2:
                location1 = details1["location"]
                location2 = details2["location"]
                travel_time = travel_times[location1][location2]
                for j in range(len(time_slots) - travel_time - 1):
                    solver.add(Implies(meeting_vars[person1][j], Not(meeting_vars[person2][j + travel_time + 1])))

# Define constraints for starting at Union Square at 9:00 AM
start_time = time_to_minutes(900)
solver.add(meeting_vars["Kimberly"][start_time - time_slots[0]])  # Start with Kimberly as an example

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, details in people.items():
        location = details["location"]
        start = None
        end = None
        for i, time in enumerate(time_slots):
            if model.evaluate(meeting_vars[person][i]):
                if start is None:
                    start = time
                end = time
        if start is not None and end is not None:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{start // 60:02}:{start % 60:02}",
                "end_time": f"{end // 60:02}:{end % 60:02}"
            })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")