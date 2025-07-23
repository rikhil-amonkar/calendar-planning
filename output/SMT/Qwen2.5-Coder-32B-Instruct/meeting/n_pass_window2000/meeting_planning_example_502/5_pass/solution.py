from z3 import *

# Define the locations and their travel times
locations = ["Financial District", "Golden Gate Park", "Chinatown", "Union Square", "Fisherman's Wharf", "Pacific Heights", "North Beach"]
travel_times = {
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "North Beach"): 3,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "North Beach"): 10,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "North Beach"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
}

# Define the meetings and their constraints
meetings = {
    "Stephanie": {"location": "Golden Gate Park", "start": 660, "end": 1800, "min_duration": 105},
    "Karen": {"location": "Chinatown", "start": 945, "end": 2610, "min_duration": 15},
    "Brian": {"location": "Union Square", "start": 1800, "end": 3090, "min_duration": 30},
    "Rebecca": {"location": "Fisherman's Wharf", "start": 480, "end": 675, "min_duration": 30},
    "Joseph": {"location": "Pacific Heights", "start": 510, "end": 570, "min_duration": 60},
    "Steven": {"location": "North Beach", "start": 1530, "end": 5070, "min_duration": 120},
}

# Convert times to minutes from 00:00
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_vars = {}
for person, details in meetings.items():
    start = Int(f"{person}_start")
    end = Int(f"{person}_end")
    meeting_vars[person] = (start, end)
    solver.add(start >= details["start"])
    solver.add(end <= details["end"])
    solver.add(end - start >= details["min_duration"])

# Ensure all meetings end before 24:00
for person, details in meetings.items():
    start, end = meeting_vars[person]
    solver.add(end <= 1440)  # 1440 minutes is 24:00

# Define a list of meeting indices
meeting_list = list(meetings.items())
num_meetings = len(meeting_list)

# Create a list of meeting indices
meeting_indices = [Int(f"meeting_{i}_index") for i in range(num_meetings)]

# Ensure each meeting index is unique and within bounds
solver.add(Distinct(meeting_indices))
for i in range(num_meetings):
    solver.add(meeting_indices[i] >= 0)
    solver.add(meeting_indices[i] < num_meetings)

# Ensure meetings are in chronological order and respect travel times
for i in range(num_meetings - 1):
    idx1 = meeting_indices[i]
    idx2 = meeting_indices[i + 1]
    person1, details1 = meeting_list[i]
    person2, details2 = meeting_list[i + 1]
    start1, end1 = meeting_vars[person1]
    start2, end2 = meeting_vars[person2]
    travel_time = travel_times[(details1["location"], details2["location"])]
    solver.add(end1 + travel_time <= start2)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person, details in meetings.items():
        start = model[meeting_vars[person][0]].as_long()
        end = model[meeting_vars[person][1]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    print({"itinerary": itinerary})
else:
    print("No solution found")