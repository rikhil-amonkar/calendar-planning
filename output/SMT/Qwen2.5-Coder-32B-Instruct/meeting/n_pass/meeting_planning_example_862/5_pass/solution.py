from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the people and their availability
people = {
    "Laura": (time_in_minutes(14, 30), time_in_minutes(16, 15)),
    "Brian": (time_in_minutes(10, 15), time_in_minutes(17, 0)),
    "Karen": (time_in_minutes(18, 0), time_in_minutes(20, 15)),
    "Stephanie": (time_in_minutes(10, 15), time_in_minutes(16, 0)),
    "Helen": (time_in_minutes(11, 30), time_in_minutes(21, 45)),
    "Sandra": (time_in_minutes(8, 0), time_in_minutes(15, 15)),
    "Mary": (time_in_minutes(16, 45), time_in_minutes(18, 45)),
    "Deborah": (time_in_minutes(19, 0), time_in_minutes(20, 45)),
    "Elizabeth": (time_in_minutes(8, 30), time_in_minutes(13, 15))
}

# Define the minimum meeting times in minutes
min_meeting_times = {
    "Laura": 75,
    "Brian": 30,
    "Karen": 90,
    "Stephanie": 75,
    "Helen": 120,
    "Sandra": 30,
    "Mary": 120,
    "Deborah": 105,
    "Elizabeth": 105
}

# Define the travel times
travel_times = {
    "Mission District": {
        "Alamo Square": 11,
        "Presidio": 25,
        "Russian Hill": 15,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Financial District": 15,
        "Marina District": 19
    },
    "Alamo Square": {
        "Mission District": 10,
        "Presidio": 17,
        "Russian Hill": 13,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Embarcadero": 16,
        "Financial District": 17,
        "Marina District": 15
    },
    "Presidio": {
        "Mission District": 26,
        "Alamo Square": 19,
        "Russian Hill": 14,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11
    },
    "Russian Hill": {
        "Mission District": 16,
        "Alamo Square": 15,
        "Presidio": 14,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7
    },
    "North Beach": {
        "Mission District": 18,
        "Alamo Square": 16,
        "Presidio": 17,
        "Russian Hill": 4,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "Alamo Square": 9,
        "Presidio": 11,
        "Russian Hill": 19,
        "North Beach": 23,
        "Richmond District": 7,
        "Embarcadero": 25,
        "Financial District": 26,
        "Marina District": 16
    },
    "Richmond District": {
        "Mission District": 20,
        "Alamo Square": 13,
        "Presidio": 7,
        "Russian Hill": 13,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "Marina District": 9
    },
    "Embarcadero": {
        "Mission District": 20,
        "Alamo Square": 19,
        "Presidio": 20,
        "Russian Hill": 8,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Financial District": 4,
        "Marina District": 12
    },
    "Financial District": {
        "Mission District": 17,
        "Alamo Square": 17,
        "Presidio": 22,
        "Russian Hill": 11,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Embarcadero": 4,
        "Marina District": 15
    },
    "Marina District": {
        "Mission District": 20,
        "Alamo Square": 15,
        "Presidio": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Financial District": 17
    }
}

# Create the solver
solver = Solver()

# Define the variables
start_times = {person: Int(f"start_{person}") for person in people}
end_times = {person: Int(f"end_{person}") for person in people}
current_location = "Mission District"
current_time = 0

# Add constraints for each person
for person, (start, end) in people.items():
    solver.add(start_times[person] >= start)
    solver.add(end_times[person] <= end)
    solver.add(end_times[person] - start_times[person] >= min_meeting_times[person])

# Add constraints for travel times
locations = list(travel_times.keys())
location_vars = {person: String(f"location_{person}") for person in people}

# Add constraints for starting location and time
solver.add(location_vars["Brian"] == "Presidio")  # Start at Presidio after 10:15AM

# Sort people by their earliest availability
sorted_people = sorted(people.items(), key=lambda x: x[1][0])

# Add constraints for sequential meetings
for i in range(len(sorted_people) - 1):
    person1, (start1, end1) = sorted_people[i]
    person2, (start2, end2) = sorted_people[i + 1]
    travel_time = travel_times[current_location][person2]
    solver.add(end_times[person1] + travel_time <= start_times[person2])
    current_location = person2

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start = model[start_times[person]].as_long()
        end = model[end_times[person]].as_long()
        start_time = f"{9 + start // 60:02}:{start % 60:02}"
        end_time = f"{9 + end // 60:02}:{end % 60:02}"
        itinerary.append({"action": "meet", "person": person, "start_time": start_time, "end_time": end_time})
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")