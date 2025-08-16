import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Russian Hill"): 5,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Russian Hill"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Russian Hill"): 18,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Russian Hill"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Russian Hill"): 8,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Marina District"): 7,
}

# Define meeting constraints
constraints = {
    "Mary": {"location": "Embarcadero", "start": "20:00", "end": "21:15", "min_duration": 75},
    "Kenneth": {"location": "The Castro", "start": "11:15", "end": "19:15", "min_duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": "20:00", "end": "22:00", "min_duration": 120},
    "Sarah": {"location": "Union Square", "start": "11:45", "end": "14:30", "min_duration": 90},
    "Thomas": {"location": "North Beach", "start": "19:15", "end": "19:45", "min_duration": 15},
    "Daniel": {"location": "Pacific Heights", "start": "13:45", "end": "20:30", "min_duration": 15},
    "Richard": {"location": "Chinatown", "start": "08:00", "end": "18:45", "min_duration": 30},
    "Mark": {"location": "Golden Gate Park", "start": "17:30", "end": "21:30", "min_duration": 120},
    "David": {"location": "Marina District", "start": "20:00", "end": "21:00", "min_duration": 60},
    "Karen": {"location": "Russian Hill", "start": "13:15", "end": "18:30", "min_duration": 120},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def find_meeting_schedule(constraints, travel_times):
    current_time = parse_time("9:00")
    current_location = "Nob Hill"
    itinerary = []

    def can_meet(constraint, current_time):
        start = parse_time(constraint["start"])
        end = parse_time(constraint["end"])
        min_duration = constraint["min_duration"]
        return start <= current_time + timedelta(minutes=min_duration) <= end

    def next_location(current_location, target_location):
        if current_location == target_location:
            return 0
        return travel_times[(current_location, target_location)]

    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["start"]))

    for name, constraint in sorted_constraints:
        location = constraint["location"]
        start = parse_time(constraint["start"])
        end = parse_time(constraint["end"])
        min_duration = constraint["min_duration"]

        travel_time = next_location(current_location, location)
        potential_start = current_time + timedelta(minutes=travel_time)

        if can_meet(constraint, potential_start):
            meeting_start = max(potential_start, start)
            meeting_end = min(meeting_start + timedelta(minutes=min_duration), end)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": time_to_str(meeting_start),
                "end_time": time_to_str(meeting_end)
            })
            current_time = meeting_end
            current_location = location

    return itinerary

itinerary = find_meeting_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result))