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
    "Kimberly": ("Marina District", 13.25, 16.75, 15),
    "Robert": ("Chinatown", 12.25, 20.25, 15),
    "Rebecca": ("Financial District", 13.25, 16.75, 75),
    "Margaret": ("Bayview", 9.5, 13.5, 30),
    "Kenneth": ("Union Square", 19.5, 21.25, 75),
}

# Convert times to minutes from start of the day
def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return hours * 60 + minutes

# Convert minutes to time in HH:MM format
def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Create a solver instance
solver = Solver()

# Define variables for the start time of each meeting
meeting_starts = {person: Int(f"start_{person}") for person in people}

# Define variables for the current district
current_district = Int("current_district")

# Define the start time of the day
start_time = time_to_minutes("09:00")

# Add constraints for each person
for person, (district, start, end, duration) in people.items():
    start_minutes = int(start * 60)
    end_minutes = int(end * 60)
    duration_minutes = duration

    # Meeting must start after the person is available and end before they leave
    solver.add(meeting_starts[person] >= start_minutes)
    solver.add(meeting_starts[person] + duration_minutes <= end_minutes)

    # Travel time constraints
    if person != "Margaret":  # Margaret is the first meeting
        for prev_person, (prev_district, _, _, _) in people.items():
            if prev_person != person:
                # If meeting with prev_person, then travel time to current person's district must be respected
                solver.add(Implies(meeting_starts[person] > meeting_starts[prev_person] + people[prev_person][3],
                                   meeting_starts[person] >= meeting_starts[prev_person] + people[prev_person][3] + travel_times[(prev_district, district)]))

# Add constraints for the start time and district
solver.add(current_district == districts.index("Richmond District"))
solver.add(meeting_starts["Margaret"] == start_time)

# Optimize the schedule
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, (district, _, _, duration) in people.items():
        start_minutes = model[meeting_starts[person]].as_long()
        end_minutes = start_minutes + duration
        itinerary.append({"action": "meet", "person": person, "start_time": minutes_to_time(start_minutes), "end_time": minutes_to_time(end_minutes)})

    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))

    print({"itinerary": itinerary})
else:
    print("No solution found")