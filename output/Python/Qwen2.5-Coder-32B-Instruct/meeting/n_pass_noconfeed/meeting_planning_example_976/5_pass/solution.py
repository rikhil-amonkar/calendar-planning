import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Embarcadero": {"Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20, "Union Square": 10, "The Castro": 25, "North Beach": 5, "Fisherman's Wharf": 6, "Marina District": 12},
    "Bayview": {"Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20, "Presidio": 32, "Union Square": 18, "The Castro": 19, "North Beach": 22, "Fisherman's Wharf": 25, "Marina District": 27},
    "Chinatown": {"Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9, "Presidio": 19, "Union Square": 7, "The Castro": 22, "North Beach": 3, "Fisherman's Wharf": 8, "Marina District": 12},
    "Alamo Square": {"Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11, "Presidio": 17, "Union Square": 14, "The Castro": 8, "North Beach": 15, "Fisherman's Wharf": 19, "Marina District": 15},
    "Nob Hill": {"Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11, "Presidio": 17, "Union Square": 7, "The Castro": 17, "North Beach": 8, "Fisherman's Wharf": 10, "Marina District": 11},
    "Presidio": {"Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19, "Nob Hill": 18, "Union Square": 22, "The Castro": 21, "North Beach": 18, "Fisherman's Wharf": 19, "Marina District": 11},
    "Union Square": {"Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15, "Nob Hill": 9, "Presidio": 24, "The Castro": 19, "North Beach": 7, "Fisherman's Wharf": 15, "Marina District": 18},
    "The Castro": {"Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8, "Nob Hill": 16, "Presidio": 20, "Union Square": 19, "North Beach": 20, "Fisherman's Wharf": 27, "Marina District": 21},
    "North Beach": {"Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16, "Nob Hill": 7, "Presidio": 17, "Union Square": 7, "The Castro": 23, "Fisherman's Wharf": 5, "Marina District": 9},
    "Fisherman's Wharf": {"Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Union Square": 13, "The Castro": 27, "North Beach": 6, "Marina District": 10},
    "Marina District": {"Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15, "Nob Hill": 12, "Presidio": 10, "Union Square": 16, "The Castro": 22, "North Beach": 11, "Fisherman's Wharf": 10}
}

# Define meeting constraints
meetings = {
    "Matthew": {"location": "Bayview", "start": "19:15", "end": "22:00", "min_duration": 120},
    "Karen": {"location": "Chinatown", "start": "19:15", "end": "21:15", "min_duration": 90},
    "Sarah": {"location": "Alamo Square", "start": "20:00", "end": "21:45", "min_duration": 105},
    "Jessica": {"location": "Nob Hill", "start": "16:30", "end": "18:45", "min_duration": 120},
    "Stephanie": {"location": "Presidio", "start": "07:30", "end": "10:15", "min_duration": 60},
    "Mary": {"location": "Union Square", "start": "16:45", "end": "21:30", "min_duration": 60},
    "Charles": {"location": "The Castro", "start": "16:30", "end": "22:00", "min_duration": 105},
    "Nancy": {"location": "North Beach", "start": "14:45", "end": "20:00", "min_duration": 15},
    "Thomas": {"location": "Fisherman's Wharf", "start": "13:30", "end": "19:00", "min_duration": 30},
    "Brian": {"location": "Marina District", "start": "12:15", "end": "18:00", "min_duration": 60}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def find_optimal_schedule(start_location, start_time):
    current_location = start_location
    current_time = parse_time(start_time)
    itinerary = []
    meetings_list = list(meetings.items())

    def can_meet(meeting, current_time):
        meeting_start = parse_time(meeting["start"])
        meeting_end = parse_time(meeting["end"])
        return meeting_start <= current_time + timedelta(minutes=meeting["min_duration"]) <= meeting_end

    # Sort meetings by their start time
    meetings_list.sort(key=lambda x: parse_time(x[1]["start"]))

    for person, details in meetings_list:
        travel_time = travel_times[current_location][details["location"]]
        potential_arrival_time = current_time + timedelta(minutes=travel_time)

        # Calculate the earliest possible meeting start time
        meeting_start_time = max(potential_arrival_time, parse_time(details["start"]))
        meeting_end_time = meeting_start_time + timedelta(minutes=details["min_duration"])

        # Check if the meeting can fit within the meeting end time
        if meeting_end_time <= parse_time(details["end"]):
            itinerary.append({
                "action": "travel",
                "to": details["location"],
                "start_time": format_time(current_time),
                "end_time": format_time(potential_arrival_time)
            })
            itinerary.append({
                "action": "meet",
                "location": details["location"],
                "person": person,
                "start_time": format_time(meeting_start_time),
                "end_time": format_time(meeting_end_time)
            })
            current_time = meeting_end_time
            current_location = details["location"]
        else:
            # If the meeting cannot be attended, skip it
            continue

    return itinerary

itinerary = find_optimal_schedule("Embarcadero", "09:00")
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))