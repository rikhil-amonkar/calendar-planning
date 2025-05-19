import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def compute_schedule():
    # Travel times dictionary: from_location -> to_location -> minutes
    travel_times = {
        "Presidio": {
            "Golden Gate Park": 12,
            "Bayview": 31,
            "Chinatown": 21,
            "North Beach": 18,
            "Mission District": 26
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Bayview": 23,
            "Chinatown": 23,
            "North Beach": 24,
            "Mission District": 17
        },
        "Bayview": {
            "Presidio": 31,
            "Golden Gate Park": 22,
            "Chinatown": 18,
            "North Beach": 21,
            "Mission District": 13
        },
        "Chinatown": {
            "Presidio": 19,
            "Golden Gate Park": 23,
            "Bayview": 22,
            "North Beach": 3,
            "Mission District": 18
        },
        "North Beach": {
            "Presidio": 17,
            "Golden Gate Park": 22,
            "Bayview": 22,
            "Chinatown": 6,
            "Mission District": 18
        },
        "Mission District": {
            "Presidio": 25,
            "Golden Gate Park": 17,
            "Bayview": 15,
            "Chinatown": 16,
            "North Beach": 17
        }
    }

    # Friend constraints
    friends = [
        {
            "name": "Jessica",
            "location": "Golden Gate Park",
            "available_start": "13:45",
            "available_end": "15:00",
            "min_duration": 30
        },
        {
            "name": "Ashley",
            "location": "Bayview",
            "available_start": "17:15",
            "available_end": "20:00",
            "min_duration": 105
        },
        {
            "name": "Ronald",
            "location": "Chinatown",
            "available_start": "7:15",
            "available_end": "14:45",
            "min_duration": 90
        },
        {
            "name": "William",
            "location": "North Beach",
            "available_start": "13:15",
            "available_end": "20:15",
            "min_duration": 15
        },
        {
            "name": "Daniel",
            "location": "Mission District",
            "available_start": "7:00",
            "available_end": "11:15",
            "min_duration": 105
        }
    ]

    current_location = "Presidio"
    current_time = parse_time("9:00")
    itinerary = []

    # Try to meet Daniel first (earliest availability)
    daniel = next(f for f in friends if f["name"] == "Daniel")
    travel_time = travel_times[current_location][daniel["location"]]
    arrival_time = current_time + timedelta(minutes=travel_time)
    available_start = parse_time(daniel["available_start"])
    available_end = parse_time(daniel["available_end"])

    if arrival_time < available_end:
        start_time = max(arrival_time, available_start)
        end_time = start_time + timedelta(minutes=daniel["min_duration"])
        if end_time <= available_end:
            itinerary.append({
                "action": "meet",
                "location": daniel["location"],
                "person": daniel["name"],
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
            current_location = daniel["location"]
            current_time = end_time
            friends.remove(daniel)

    # Try to meet Ronald next
    ronald = next(f for f in friends if f["name"] == "Ronald")
    travel_time = travel_times[current_location][ronald["location"]]
    arrival_time = current_time + timedelta(minutes=travel_time)
    available_start = parse_time(ronald["available_start"])
    available_end = parse_time(ronald["available_end"])

    if arrival_time < available_end:
        start_time = max(arrival_time, available_start)
        end_time = start_time + timedelta(minutes=ronald["min_duration"])
        if end_time <= available_end:
            itinerary.append({
                "action": "meet",
                "location": ronald["location"],
                "person": ronald["name"],
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
            current_location = ronald["location"]
            current_time = end_time
            friends.remove(ronald)

    # Try to meet Jessica next
    jessica = next(f for f in friends if f["name"] == "Jessica")
    travel_time = travel_times[current_location][jessica["location"]]
    arrival_time = current_time + timedelta(minutes=travel_time)
    available_start = parse_time(jessica["available_start"])
    available_end = parse_time(jessica["available_end"])

    if arrival_time < available_end:
        start_time = max(arrival_time, available_start)
        end_time = start_time + timedelta(minutes=jessica["min_duration"])
        if end_time <= available_end:
            itinerary.append({
                "action": "meet",
                "location": jessica["location"],
                "person": jessica["name"],
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
            current_location = jessica["location"]
            current_time = end_time
            friends.remove(jessica)

    # Try to meet William next
    william = next(f for f in friends if f["name"] == "William")
    travel_time = travel_times[current_location][william["location"]]
    arrival_time = current_time + timedelta(minutes=travel_time)
    available_start = parse_time(william["available_start"])
    available_end = parse_time(william["available_end"])

    if arrival_time < available_end:
        start_time = max(arrival_time, available_start)
        end_time = start_time + timedelta(minutes=william["min_duration"])
        if end_time <= available_end:
            itinerary.append({
                "action": "meet",
                "location": william["location"],
                "person": william["name"],
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
            current_location = william["location"]
            current_time = end_time
            friends.remove(william)

    # Try to meet Ashley last
    ashley = next(f for f in friends if f["name"] == "Ashley")
    travel_time = travel_times[current_location][ashley["location"]]
    arrival_time = current_time + timedelta(minutes=travel_time)
    available_start = parse_time(ashley["available_start"])
    available_end = parse_time(ashley["available_end"])

    if arrival_time < available_end:
        start_time = max(arrival_time, available_start)
        end_time = start_time + timedelta(minutes=ashley["min_duration"])
        if end_time <= available_end:
            itinerary.append({
                "action": "meet",
                "location": ashley["location"],
                "person": ashley["name"],
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })

    return {"itinerary": itinerary}

result = compute_schedule()
print(json.dumps(result, indent=2))