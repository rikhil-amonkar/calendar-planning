from z3 import *

# Define the districts and their travel times
districts = ["Richmond District", "Marina District", "Chinatown", "Financial District", "Bayview", "Union Square"]
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

# Define the people and their availability
people = {
    "Kimberly": {"district": "Marina District", "start": 13.25, "end": 16.75, "min_meeting": 0.25},
    "Robert": {"district": "Chinatown", "start": 12.25, "end": 20.25, "min_meeting": 0.25},
    "Rebecca": {"district": "Financial District", "start": 13.25, "end": 16.75, "min_meeting": 1.25},
    "Margaret": {"district": "Bayview", "start": 9.5, "end": 13.5, "min_meeting": 0.5},
    "Kenneth": {"district": "Union Square", "start": 19.5, "end": 21.25, "min_meeting": 1.25},
}

# Create a solver
solver = Solver()

# Define the variables
current_district = String('current_district')
current_time = Real('current_time')
meetings = []

# Initial conditions
solver.add(current_district == "Richmond District")
solver.add(current_time == 9.0)

# Define the meeting variables and constraints
for person, details in people.items():
    meet_start = Real(f'meet_start_{person}')
    meet_end = Real(f'meet_end_{person}')
    meet_district = String(f'meet_district_{person}')
    
    # Add constraints for meeting times
    solver.add(meet_start >= details["start"])
    solver.add(meet_end <= details["end"])
    solver.add(meet_end - meet_start >= details["min_meeting"])
    solver.add(meet_district == details["district"])
    
    # Add constraints for travel time
    solver.add(current_time + travel_times[(current_district, meet_district)] / 60.0 <= meet_start)
    
    # Update current district and time after meeting
    current_district = meet_district
    current_time = meet_end
    
    # Add meeting to the list
    meetings.append({"action": "meet", "person": person, "start_time": meet_start, "end_time": meet_end})

# Function to convert time in hours to HH:MM format
def time_to_str(time):
    hours = int(time)
    minutes = int((time - hours) * 60)
    return f"{hours:02}:{minutes:02}"

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for meeting in meetings:
        start_time = model.evaluate(meeting["start_time"]).as_decimal(2)
        end_time = model.evaluate(meeting["end_time"]).as_decimal(2)
        itinerary.append({
            "action": meeting["action"],
            "person": meeting["person"],
            "start_time": time_to_str(float(start_time)),
            "end_time": time_to_str(float(end_time))
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")