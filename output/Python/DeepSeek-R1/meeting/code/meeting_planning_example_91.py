import json
from datetime import datetime

def time_to_min(time_str):
    time_obj = datetime.strptime(time_str, "%I:%M%p")
    return time_obj.hour * 60 + time_obj.minute

def min_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02}"

travel_times = {
    ('Russian Hill', 'Richmond District'): 14,
    ('Richmond District', 'Russian Hill'): 13
}

start_location = 'Russian Hill'
start_time_str = '9:00AM'
daniel_location = 'Richmond District'
daniel_available_start_str = '7:00PM'
daniel_available_end_str = '8:15PM'
required_duration = 75

start_time = time_to_min(start_time_str)
daniel_start = time_to_min(daniel_available_start_str)
daniel_end = time_to_min(daniel_available_end_str)
available_duration = daniel_end - daniel_start

itinerary = []

if available_duration >= required_duration:
    travel_time = travel_times.get((start_location, daniel_location), 0)
    departure_time = daniel_start - travel_time
    if departure_time >= start_time:
        meet_end = min(daniel_start + required_duration, daniel_end)
        itinerary.append({
            "action": "meet",
            "location": daniel_location,
            "person": "Daniel",
            "start_time": min_to_time(daniel_start),
            "end_time": min_to_time(meet_end)
        })

print(json.dumps({"itinerary": itinerary}, indent=2))