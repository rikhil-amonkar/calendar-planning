import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Haight-Ashbury"): 18,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19
}

# Meeting constraints
constraints = {
    "Kimberly": {"location": "Presidio", "start_time": "15:30", "end_time": "16:00", "duration": 30},
    "Elizabeth": {"location": "Alamo Square", "start_time": "19:15", "end_time": "20:15", "duration": 60},
    "Joshua": {"location": "Marina District", "start_time": "10:30", "end_time": "14:15", "duration": 180},
    "Sandra": {"location": "Financial District", "start_time": "19:30", "end_time": "20:15", "duration": 45},
    "Kenneth": {"location": "Nob Hill", "start_time": "12:45", "end_time": "21:45", "duration": 210},
    "Betty": {"location": "Sunset District", "start_time": "14:00", "end_time": "19:00", "duration": 180},
    "Deborah": {"location": "Chinatown", "start_time": "17:15", "end_time": "20:30", "duration": 75},
    "Barbara": {"location": "Russian Hill", "start_time": "17:30", "end_time": "21:15", "duration": 270},
    "Steven": {"location": "North Beach", "start_time": "17:45", "end_time": "20:45", "duration": 180},
    "Daniel": {"location": "Haight-Ashbury", "start_time": "18:30", "end_time": "18:45", "duration": 15}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances.get((start_location, end_location), 0)

def is_meeting_possible(start_time, end_time, duration, location, person):
    person_start_time = datetime.strptime(constraints[person]["start_time"], "%H:%M")
    person_end_time = datetime.strptime(constraints[person]["end_time"], "%H:%M")
    travel_time_to_location = calculate_travel_time("Union Square", location)
    travel_time_from_location = calculate_travel_time(location, "Union Square")
    if start_time >= person_start_time - timedelta(minutes=travel_time_to_location) and end_time <= person_end_time + timedelta(minutes=travel_time_from_location):
        return True
    return False

def find_meetings():
    meetings = []
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("09:00", "%H:%M")
    for person in constraints:
        location = constraints[person]["location"]
        person_start_time = datetime.strptime(constraints[person]["start_time"], "%H:%M")
        person_end_time = datetime.strptime(constraints[person]["end_time"], "%H:%M")
        if is_meeting_possible(start_time, end_time, constraints[person]["duration"], location, person):
            travel_time_to_location = calculate_travel_time("Union Square", location)
            travel_time_from_location = calculate_travel_time(location, "Union Square")
            start_time = max(start_time, person_start_time - timedelta(minutes=travel_time_to_location))
            end_time = start_time + timedelta(minutes=constraints[person]["duration"])
            meetings.append({"action": "meet", "location": location, "person": person, "start_time": start_time.strftime("%H:%M"), "end_time": end_time.strftime("%H:%M")})
    return meetings

def main():
    meetings = find_meetings()
    itinerary = {"itinerary": meetings}
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()