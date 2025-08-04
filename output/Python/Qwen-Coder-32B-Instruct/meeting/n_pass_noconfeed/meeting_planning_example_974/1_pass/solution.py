import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Sunset District", "Presidio"): 16, ("Presidio", "Sunset District"): 15,
    ("Sunset District", "Nob Hill"): 27, ("Nob Hill", "Sunset District"): 24,
    ("Sunset District", "Pacific Heights"): 21, ("Pacific Heights", "Sunset District"): 21,
    ("Sunset District", "Mission District"): 25, ("Mission District", "Sunset District"): 24,
    ("Sunset District", "Marina District"): 21, ("Marina District", "Sunset District"): 19,
    ("Sunset District", "North Beach"): 28, ("North Beach", "Sunset District"): 27,
    ("Sunset District", "Russian Hill"): 24, ("Russian Hill", "Sunset District"): 23,
    ("Sunset District", "Richmond District"): 12, ("Richmond District", "Sunset District"): 11,
    ("Sunset District", "Embarcadero"): 30, ("Embarcadero", "Sunset District"): 30,
    ("Sunset District", "Alamo Square"): 17, ("Alamo Square", "Sunset District"): 16,
    ("Presidio", "Nob Hill"): 18, ("Nob Hill", "Presidio"): 17,
    ("Presidio", "Pacific Heights"): 11, ("Pacific Heights", "Presidio"): 11,
    ("Presidio", "Mission District"): 26, ("Mission District", "Presidio"): 25,
    ("Presidio", "Marina District"): 11, ("Marina District", "Presidio"): 10,
    ("Presidio", "North Beach"): 18, ("North Beach", "Presidio"): 17,
    ("Presidio", "Russian Hill"): 14, ("Russian Hill", "Presidio"): 14,
    ("Presidio", "Richmond District"): 7, ("Richmond District", "Presidio"): 7,
    ("Presidio", "Embarcadero"): 20, ("Embarcadero", "Presidio"): 20,
    ("Presidio", "Alamo Square"): 19, ("Alamo Square", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8, ("Pacific Heights", "Nob Hill"): 8,
    ("Nob Hill", "Mission District"): 13, ("Mission District", "Nob Hill"): 12,
    ("Nob Hill", "Marina District"): 11, ("Marina District", "Nob Hill"): 12,
    ("Nob Hill", "North Beach"): 8, ("North Beach", "Nob Hill"): 7,
    ("Nob Hill", "Russian Hill"): 5, ("Russian Hill", "Nob Hill"): 5,
    ("Nob Hill", "Richmond District"): 14, ("Richmond District", "Nob Hill"): 17,
    ("Nob Hill", "Embarcadero"): 9, ("Embarcadero", "Nob Hill"): 10,
    ("Nob Hill", "Alamo Square"): 11, ("Alamo Square", "Nob Hill"): 11,
    ("Pacific Heights", "Mission District"): 15, ("Mission District", "Pacific Heights"): 16,
    ("Pacific Heights", "Marina District"): 6, ("Marina District", "Pacific Heights"): 7,
    ("Pacific Heights", "North Beach"): 9, ("North Beach", "Pacific Heights"): 8,
    ("Pacific Heights", "Russian Hill"): 7, ("Russian Hill", "Pacific Heights"): 7,
    ("Pacific Heights", "Richmond District"): 12, ("Richmond District", "Pacific Heights"): 10,
    ("Pacific Heights", "Embarcadero"): 10, ("Embarcadero", "Pacific Heights"): 11,
    ("Pacific Heights", "Alamo Square"): 10, ("Alamo Square", "Pacific Heights"): 10,
    ("Mission District", "Marina District"): 19, ("Marina District", "Mission District"): 20,
    ("Mission District", "North Beach"): 17, ("North Beach", "Mission District"): 18,
    ("Mission District", "Russian Hill"): 15, ("Russian Hill", "Mission District"): 16,
    ("Mission District", "Richmond District"): 20, ("Richmond District", "Mission District"): 20,
    ("Mission District", "Embarcadero"): 19, ("Embarcadero", "Mission District"): 20,
    ("Mission District", "Alamo Square"): 11, ("Alamo Square", "Mission District"): 10,
    ("Marina District", "North Beach"): 11, ("North Beach", "Marina District"): 9,
    ("Marina District", "Russian Hill"): 8, ("Russian Hill", "Marina District"): 7,
    ("Marina District", "Richmond District"): 11, ("Richmond District", "Marina District"): 9,
    ("Marina District", "Embarcadero"): 14, ("Embarcadero", "Marina District"): 12,
    ("Marina District", "Alamo Square"): 15, ("Alamo Square", "Marina District"): 15,
    ("North Beach", "Russian Hill"): 4, ("Russian Hill", "North Beach"): 5,
    ("North Beach", "Richmond District"): 18, ("Richmond District", "North Beach"): 17,
    ("North Beach", "Embarcadero"): 6, ("Embarcadero", "North Beach"): 5,
    ("North Beach", "Alamo Square"): 16, ("Alamo Square", "North Beach"): 15,
    ("Russian Hill", "Richmond District"): 14, ("Richmond District", "Russian Hill"): 13,
    ("Russian Hill", "Embarcadero"): 8, ("Embarcadero", "Russian Hill"): 8,
    ("Russian Hill", "Alamo Square"): 15, ("Alamo Square", "Russian Hill"): 13,
    ("Richmond District", "Embarcadero"): 19, ("Embarcadero", "Richmond District"): 21,
    ("Richmond District", "Alamo Square"): 13, ("Alamo Square", "Richmond District"): 11,
    ("Embarcadero", "Alamo Square"): 19, ("Alamo Square", "Embarcadero"): 16,
}

# Define meeting constraints
meetings = {
    "Charles": {"location": "Presidio", "start": "13:15", "end": "15:00", "min_duration": 105},
    "Robert": {"location": "Nob Hill", "start": "13:15", "end": "17:30", "min_duration": 90},
    "Nancy": {"location": "Pacific Heights", "start": "14:45", "end": "22:00", "min_duration": 105},
    "Brian": {"location": "Mission District", "start": "15:30", "end": "22:00", "min_duration": 60},
    "Kimberly": {"location": "Marina District", "start": "17:00", "end": "19:45", "min_duration": 75},
    "David": {"location": "North Beach", "start": "14:45", "end": "16:30", "min_duration": 75},
    "William": {"location": "Russian Hill", "start": "12:30", "end": "19:15", "min_duration": 120},
    "Jeffrey": {"location": "Richmond District", "start": "12:00", "end": "19:15", "min_duration": 45},
    "Karen": {"location": "Embarcadero", "start": "14:15", "end": "20:45", "min_duration": 60},
    "Joshua": {"location": "Alamo Square", "start": "18:45", "end": "22:00", "min_duration": 60},
}

# Convert times to datetime objects
def convert_to_datetime(time_str, base_date):
    return datetime.strptime(f"{base_date} {time_str}", "%Y-%m-%d %H:%M")

# Check if a meeting can be scheduled
def can_meet(start_time, end_time, meeting_start, meeting_end, min_duration):
    meeting_start_time = convert_to_datetime(meeting_start, start_time.date())
    meeting_end_time = convert_to_datetime(meeting_end, start_time.date())
    available_time = end_time - start_time
    meeting_duration = meeting_end_time - meeting_start_time
    return available_time.total_seconds() >= min_duration * 60 and meeting_duration.total_seconds() >= min_duration * 60

# Find the best meeting time within constraints
def find_best_meeting_time(start_time, end_time, meeting_start, meeting_end, min_duration):
    meeting_start_time = convert_to_datetime(meeting_start, start_time.date())
    meeting_end_time = convert_to_datetime(meeting_end, start_time.date())
    if meeting_start_time < start_time:
        meeting_start_time = start_time
    if meeting_end_time > end_time:
        meeting_end_time = end_time
    if (meeting_end_time - meeting_start_time).total_seconds() >= min_duration * 60:
        return meeting_start_time, meeting_start_time + timedelta(minutes=min_duration)
    return None, None

# Main function to compute the optimal schedule
def compute_optimal_schedule():
    start_time = convert_to_datetime("9:00", "2023-10-01")
    current_time = start_time
    itinerary = []
    visited_locations = set()

    while current_time < convert_to_datetime("22:00", "2023-10-01"):
        next_meeting = None
        next_location = None
        next_person = None
        next_start_time = None
        next_end_time = None

        for person, details in meetings.items():
            location = details["location"]
            meeting_start = details["start"]
            meeting_end = details["end"]
            min_duration = details["min_duration"]

            if location in visited_locations:
                continue

            best_start, best_end = find_best_meeting_time(current_time, convert_to_datetime("22:00", "2023-10-01"), meeting_start, meeting_end, min_duration)
            if best_start and best_end:
                travel_time = travel_times.get((current_time.strftime("%H:%M"), location), float('inf'))
                if best_start - current_time >= timedelta(minutes=travel_time):
                    if not next_meeting or best_end < next_end_time:
                        next_meeting = (best_start, best_end)
                        next_location = location
                        next_person = person
                        next_start_time = best_start
                        next_end_time = best_end

        if next_meeting:
            travel_time = travel_times.get((current_time.strftime("%H:%M"), next_location), float('inf'))
            travel_duration = timedelta(minutes=travel_time)
            current_time += travel_duration
            itinerary.append({
                "action": "travel",
                "location": next_location,
                "person": None,
                "start_time": current_time.strftime("%H:%M"),
                "end_time": (current_time + travel_duration).strftime("%H:%M")
            })
            current_time = next_start_time
            itinerary.append({
                "action": "meet",
                "location": next_location,
                "person": next_person,
                "start_time": current_time.strftime("%H:%M"),
                "end_time": next_end_time.strftime("%H:%M")
            })
            current_time = next_end_time
            visited_locations.add(next_location)
        else:
            break

    return itinerary

# Generate the optimal schedule
optimal_itinerary = compute_optimal_schedule()

# Output the result as JSON
output = {
    "itinerary": optimal_itinerary
}
print(json.dumps(output, indent=2))