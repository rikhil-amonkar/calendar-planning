import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = datetime.strptime("9:00", "%H:%M")
travel_times = {
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Russian Hill"): 4,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Russian Hill"): 13,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11
}
meetings = {
    "Emily": {"location": "Union Square", "start_time": datetime.strptime("16:00", "%H:%M"), "end_time": datetime.strptime("17:15", "%H:%M"), "min_duration": 45},
    "Margaret": {"location": "Russian Hill", "start_time": datetime.strptime("19:00", "%H:%M"), "end_time": datetime.strptime("21:00", "%H:%M"), "min_duration": 120}
}

def format_time(time):
    return time.strftime("%H:%M").lstrip('0')

def calculate_schedule(arrival_time, travel_times, meetings):
    current_time = arrival_time
    current_location = "North Beach"
    itinerary = []

    def can_meet(meeting, current_time, current_location):
        travel_time = travel_times.get((current_location, meeting["location"]), float('inf'))
        start_time = meeting["start_time"]
        end_time = meeting["end_time"]
        min_duration = meeting["min_duration"]
        available_start = current_time + timedelta(minutes=travel_time)
        if available_start < start_time:
            available_start = start_time
        available_end = available_start + timedelta(minutes=min_duration)
        return available_end <= end_time

    for person, meeting in meetings.items():
        if can_meet(meeting, current_time, current_location):
            travel_time = travel_times[(current_location, meeting["location"])]
            current_time += timedelta(minutes=travel_time)
            start_time = max(current_time, meeting["start_time"])
            end_time = start_time + timedelta(minutes=meeting["min_duration"])
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": person,
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
            current_time = end_time
            current_location = meeting["location"]

    return itinerary

itinerary = calculate_schedule(arrival_time, travel_times, meetings)
result = {"itinerary": itinerary}
print(json.dumps(result))