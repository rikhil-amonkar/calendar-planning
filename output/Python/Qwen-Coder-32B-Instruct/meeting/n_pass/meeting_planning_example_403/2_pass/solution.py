import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Union Square": {"Golden Gate Park": 22, "Pacific Heights": 15, "Presidio": 24, "Chinatown": 7, "The Castro": 19},
    "Golden Gate Park": {"Union Square": 22, "Pacific Heights": 16, "Presidio": 11, "Chinatown": 23, "The Castro": 13},
    "Pacific Heights": {"Union Square": 12, "Golden Gate Park": 15, "Presidio": 11, "Chinatown": 11, "The Castro": 16},
    "Presidio": {"Union Square": 22, "Golden Gate Park": 12, "Pacific Heights": 11, "Chinatown": 19, "The Castro": 21},
    "Chinatown": {"Union Square": 7, "Golden Gate Park": 23, "Pacific Heights": 11, "Presidio": 19, "The Castro": 22},
    "The Castro": {"Union Square": 19, "Golden Gate Park": 11, "Pacific Heights": 16, "Presidio": 20, "Chinatown": 20}
}

# Define meeting constraints
meetings = {
    "Andrew": {"location": "Golden Gate Park", "start": "11:45", "end": "14:30", "min_duration": 75},
    "Sarah": {"location": "Pacific Heights", "start": "16:15", "end": "18:45", "min_duration": 15},
    "Nancy": {"location": "Presidio", "start": "17:30", "end": "19:15", "min_duration": 60},
    "Rebecca": {"location": "Chinatown", "start": "9:45", "end": "21:30", "min_duration": 90},
    "Robert": {"location": "The Castro", "start": "8:30", "end": "14:15", "min_duration": 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def find_optimal_schedule():
    current_location = "Union Square"
    current_time = parse_time("9:00")
    itinerary = []

    def can_meet(person, start, end, min_duration, current_time):
        meeting_start = max(current_time, parse_time(start))
        meeting_end = meeting_start + timedelta(minutes=min_duration)
        return meeting_end <= parse_time(end)

    def add_meeting_to_itinerary(person, location, start, end, min_duration, current_time):
        meeting_start = max(current_time, parse_time(start))
        meeting_end = meeting_start + timedelta(minutes=min_duration)
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": time_to_str(meeting_start),
            "end_time": time_to_str(meeting_end)
        })
        return meeting_end

    # Prioritize meetings based on constraints
    priority_order = ["Rebecca", "Robert", "Andrew", "Nancy", "Sarah"]

    for person in priority_order:
        details = meetings[person]
        if can_meet(person, details["start"], details["end"], details["min_duration"], current_time):
            travel_time = travel_times[current_location][details["location"]]
            arrival_time = current_time + timedelta(minutes=travel_time)
            if can_meet(person, details["start"], details["end"], details["min_duration"], arrival_time):
                current_time = add_meeting_to_itinerary(person, details["location"], details["start"], details["end"], details["min_duration"], arrival_time)
                current_location = details["location"]

    return itinerary

optimal_itinerary = find_optimal_schedule()
output = {"itinerary": optimal_itinerary}
print(json.dumps(output, indent=2))