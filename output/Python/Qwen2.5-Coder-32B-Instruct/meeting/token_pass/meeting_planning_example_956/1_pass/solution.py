import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 12,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Pacific Heights"): 16,
}

# Define meeting constraints
constraints = {
    "William": {"location": "Alamo Square", "start": "15:15", "end": "17:15", "duration": 60},
    "Joshua": {"location": "Richmond District", "start": "07:00", "end": "20:00", "duration": 15},
    "Joseph": {"location": "Financial District", "start": "11:15", "end": "13:30", "duration": 15},
    "David": {"location": "Union Square", "start": "16:45", "end": "19:15", "duration": 45},
    "Brian": {"location": "Fisherman's Wharf", "start": "13:45", "end": "20:45", "duration": 105},
    "Karen": {"location": "Marina District", "start": "11:30", "end": "18:30", "duration": 15},
    "Anthony": {"location": "Haight-Ashbury", "start": "07:15", "end": "10:30", "duration": 30},
    "Matthew": {"location": "Mission District", "start": "17:15", "end": "19:15", "duration": 120},
    "Helen": {"location": "Pacific Heights", "start": "08:00", "end": "12:00", "duration": 75},
    "Jeffrey": {"location": "Golden Gate Park", "start": "19:00", "end": "21:30", "duration": 60},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def find_next_meeting(current_location, current_time, remaining_constraints):
    best_meeting = None
    for person, constraint in remaining_constraints.items():
        location = constraint["location"]
        start_time = parse_time(constraint["start"])
        end_time = parse_time(constraint["end"])
        duration = constraint["duration"]

        # Calculate travel time
        if (current_location, location) in travel_times:
            travel_time = travel_times[(current_location, location)]
        else:
            continue

        # Calculate potential meeting start and end times
        potential_start = current_time + timedelta(minutes=travel_time)
        potential_end = potential_start + timedelta(minutes=duration)

        # Check if meeting fits within person's availability
        if start_time <= potential_start <= end_time and potential_end <= end_time:
            if best_meeting is None or potential_end - potential_start > best_meeting[2]:
                best_meeting = (person, location, potential_end - potential_start, potential_start, potential_end)

    return best_meeting

def generate_itinerary(start_location, start_time_str):
    current_location = start_location
    current_time = parse_time(start_time_str)
    remaining_constraints = constraints.copy()
    itinerary = []

    while remaining_constraints:
        next_meeting = find_next_meeting(current_location, current_time, remaining_constraints)
        if next_meeting is None:
            break

        person, location, _, start_time, end_time = next_meeting
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })
        current_location = location
        current_time = end_time
        del remaining_constraints[person]

    return itinerary

# Generate and print the itinerary
itinerary = generate_itinerary("The Castro", "09:00")
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))