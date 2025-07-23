# Define the locations
locations = ["Sunset District", "Russian Hill", "The Castro", "Richmond District", "Marina District", "North Beach", "Union Square", "Golden Gate Park"]

# Define the travel times
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Union Square"): 22,
}

# Define the people and their availability
people = {
    "Karen": {"location": "Russian Hill", "start": 2045, "end": 2145, "min_duration": 60},
    "Jessica": {"location": "The Castro", "start": 1545, "end": 1930, "min_duration": 60},
    "Matthew": {"location": "Richmond District", "start": 730, "end": 1515, "min_duration": 15},
    "Michelle": {"location": "Marina District", "start": 1030, "end": 1845, "min_duration": 75},
    "Carol": {"location": "North Beach", "start": 1200, "end": 1700, "min_duration": 90},
    "Stephanie": {"location": "Union Square", "start": 1045, "end": 1415, "min_duration": 30},
    "Linda": {"location": "Golden Gate Park", "start": 1045, "end": 2200, "min_duration": 90},
}

# Convert times to minutes from 00:00
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Function to find the next meeting
def find_next_meeting(current_time, current_location, remaining_people):
    best_meeting = None
    best_end_time = float('inf')
    for person, details in remaining_people.items():
        start_time = time_to_minutes(details["start"])
        end_time = time_to_minutes(details["end"])
        min_duration = details["min_duration"]
        location = details["location"]
        travel_time = travel_times.get((current_location, location), 0)
        meeting_start = max(current_time + travel_time, start_time)
        meeting_end = meeting_start + min_duration
        if meeting_end <= end_time and meeting_end < best_end_time:
            best_meeting = person
            best_end_time = meeting_end
    return best_meeting, best_end_time

# Initialize the schedule
current_time = time_to_minutes(900)  # 9:00 AM
current_location = "Sunset District"
remaining_people = people.copy()
itinerary = []

# Schedule meetings
while remaining_people:
    next_meeting, next_end_time = find_next_meeting(current_time, current_location, remaining_people)
    if next_meeting is None:
        break
    itinerary.append({
        "action": "meet",
        "person": next_meeting,
        "start_time": f"{current_time // 60:02}:{current_time % 60:02}",
        "end_time": f"{next_end_time // 60:02}:{next_end_time % 60:02}"
    })
    current_time = next_end_time
    current_location = people[next_meeting]["location"]
    del remaining_people[next_meeting]

# Ensure the final meeting with Karen is scheduled for at least 60 minutes between 8:45 PM and 9:45 PM
karen_start = time_to_minutes(2045)
karen_end = time_to_minutes(2145)
karen_min_duration = 60

# Check if Karen can be scheduled
if current_time + karen_min_duration <= karen_end:
    itinerary.append({
        "action": "meet",
        "person": "Karen",
        "start_time": f"{current_time // 60:02}:{current_time % 60:02}",
        "end_time": f"{(current_time + karen_min_duration) // 60:02}:{(current_time + karen_min_duration) % 60:02}"
    })

# Print the itinerary
print({"itinerary": itinerary})