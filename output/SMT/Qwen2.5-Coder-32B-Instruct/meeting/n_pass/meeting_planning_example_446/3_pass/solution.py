from z3 import *

# Define the districts and their travel times
districts = ["Richmond District", "Marina District", "Chinatown", "Financial District", "Bayview", "Union Square"]
district_to_index = {district: i for i, district in enumerate(districts)}
travel_times = {
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Bayview"): 26,
    ("Richmond District", "Union Square"): 21,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Chinatown"): 16,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Union Square"): 7,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Union Square"): 9,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Union Square"): 17,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Bayview"): 15,
}

# Define the friends and their availability
friends = {
    "Kimberly": {"district": "Marina District", "start": 13.25, "end": 16.75, "min_duration": 0.25},
    "Robert": {"district": "Chinatown", "start": 12.25, "end": 20.25, "min_duration": 0.25},
    "Rebecca": {"district": "Financial District", "start": 13.25, "end": 16.75, "min_duration": 1.25},
    "Margaret": {"district": "Bayview", "start": 9.5, "end": 13.5, "min_duration": 0.5},
    "Kenneth": {"district": "Union Square", "start": 19.5, "end": 21.25, "min_duration": 1.25},
}

# Convert times to minutes for easier calculations
def time_to_minutes(time):
    hours, minutes = divmod(time * 60, 60)
    return int(hours * 60 + minutes)

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_vars = {}
for friend, details in friends.items():
    start = Int(f"{friend}_start")
    end = Int(f"{friend}_end")
    meeting_vars[friend] = (start, end)
    solver.add(start >= time_to_minutes(details["start"]))
    solver.add(end <= time_to_minutes(details["end"]))
    solver.add(end - start >= time_to_minutes(details["min_duration"]))

# Define variables for the current district and time
current_district = Int("current_district")
current_time = Int("current_time")
solver.add(current_district == district_to_index["Richmond District"])
solver.add(current_time == time_to_minutes(9.0))

# Define constraints for traveling between districts
for friend, (start, end) in meeting_vars.items():
    district = friends[friend]["district"]
    district_index = district_to_index[district]
    travel_time = travel_times[(districts[current_district.as_long()], districts[district_index])]
    solver.add(current_time + travel_time <= start)
    current_time = end
    current_district = district_index

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    current_time_value = model[current_time].as_long()
    current_district_value = model[current_district].as_long()
    
    for friend, (start, end) in meeting_vars.items():
        start_time = model[start].as_long() / 60
        end_time = model[end].as_long() / 60
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": f"{int(start_time):02}:{int((start_time % 1) * 60):02}",
            "end_time": f"{int(end_time):02}:{int((end_time % 1) * 60):02}"
        })
    
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")