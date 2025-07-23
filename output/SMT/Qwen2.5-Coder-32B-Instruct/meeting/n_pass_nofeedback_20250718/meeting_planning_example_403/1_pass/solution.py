from z3 import *

# Define the locations and their travel times
locations = ["Union Square", "Golden Gate Park", "Pacific Heights", "Presidio", "Chinatown", "The Castro"]
travel_times = {
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "The Castro"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "The Castro"): 22,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
}

# Define the people and their availability
people = {
    "Andrew": {"location": "Golden Gate Park", "start": 11.75, "end": 14.5, "min_meeting": 1.25},
    "Sarah": {"location": "Pacific Heights", "start": 16.25, "end": 18.75, "min_meeting": 0.25},
    "Nancy": {"location": "Presidio", "start": 17.5, "end": 18.25, "min_meeting": 1.0},
    "Rebecca": {"location": "Chinatown", "start": 9.75, "end": 21.5, "min_meeting": 1.5},
    "Robert": {"location": "The Castro", "start": 8.5, "end": 14.25, "min_meeting": 0.5},
}

# Convert times to minutes for easier calculations
def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Create a solver instance
solver = Solver()

# Define the start time for each person's meeting
meeting_starts = {person: Int(f"start_{person}") for person in people}

# Define the location at each time step
current_location = Int("current_location")
current_time = Int("current_time")

# Initial conditions
solver.add(current_location == locations.index("Union Square"))
solver.add(current_time == time_to_minutes("09:00"))

# Constraints for each person
for person, details in people.items():
    loc_index = locations.index(details["location"])
    start_time = time_to_minutes("09:00")
    end_time = time_to_minutes("21:00")
    meeting_start = meeting_starts[person]
    meeting_end = meeting_start + int(details["min_meeting"] * 60)
    
    # Person must be at their location during their meeting time
    solver.add(meeting_start >= time_to_minutes(minutes_to_time(int(details["start"] * 60))))
    solver.add(meeting_end <= time_to_minutes(minutes_to_time(int(details["end"] * 60))))
    
    # Travel constraints
    solver.add(current_time + travel_times[(locations[current_location], details["location"])] <= meeting_start)
    solver.add(meeting_end + travel_times[(details["location"], locations[current_location])] <= end_time)
    
    # Update current location and time after meeting
    current_location = loc_index
    current_time = meeting_end

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, details in people.items():
        start = model[meeting_starts[person]].as_long()
        end = start + int(details["min_meeting"] * 60)
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    print({"itinerary": itinerary})
else:
    print("No solution found")