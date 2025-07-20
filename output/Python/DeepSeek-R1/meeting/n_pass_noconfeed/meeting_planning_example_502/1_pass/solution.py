import itertools
import json

def time_to_minutes(time_str):
    time_str = time_str.strip().upper()
    if time_str.endswith("AM") or time_str.endswith("PM"):
        period = time_str[-2:]
        time_part = time_str[:-2].strip()
    else:
        period = ""
        time_part = time_str
    parts = time_part.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    if period == "PM" and hour != 12:
        hour += 12
    elif period == "AM" and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

travel_time = {
    "Financial District": {"Golden Gate Park": 23, "Chinatown": 5, "Union Square": 9, "Fisherman's Wharf": 10, "Pacific Heights": 13, "North Beach": 7},
    "Golden Gate Park": {"Financial District": 26, "Chinatown": 23, "Union Square": 22, "Fisherman's Wharf": 24, "Pacific Heights": 16, "North Beach": 24},
    "Chinatown": {"Financial District": 5, "Golden Gate Park": 23, "Union Square": 7, "Fisherman's Wharf": 8, "Pacific Heights": 10, "North Beach": 3},
    "Union Square": {"Financial District": 9, "Golden Gate Park": 22, "Chinatown": 7, "Fisherman's Wharf": 15, "Pacific Heights": 15, "North Beach": 10},
    "Fisherman's Wharf": {"Financial District": 11, "Golden Gate Park": 25, "Chinatown": 12, "Union Square": 13, "Pacific Heights": 12, "North Beach": 6},
    "Pacific Heights": {"Financial District": 13, "Golden Gate Park": 15, "Chinatown": 11, "Union Square": 12, "Fisherman's Wharf": 13, "North Beach": 9},
    "North Beach": {"Financial District": 8, "Golden Gate Park": 22, "Chinatown": 6, "Union Square": 7, "Fisherman's Wharf": 5, "Pacific Heights": 8}
}

meetings = [
    {"person": "Rebecca", "location": "Fisherman's Wharf", "avail_start": time_to_minutes("8:00AM"), "avail_end": time_to_minutes("11:15AM"), "min_dur": 30},
    {"person": "Stephanie", "location": "Golden Gate Park", "avail_start": time_to_minutes("11:00AM"), "avail_end": time_to_minutes("3:00PM"), "min_dur": 105},
    {"person": "Karen", "location": "Chinatown", "avail_start": time_to_minutes("1:45PM"), "avail_end": time_to_minutes("4:30PM"), "min_dur": 15},
    {"person": "Brian", "location": "Union Square", "avail_start": time_to_minutes("3:00PM"), "avail_end": time_to_minutes("5:15PM"), "min_dur": 30},
    {"person": "Steven", "location": "North Beach", "avail_start": time_to_minutes("2:30PM"), "avail_end": time_to_minutes("8:45PM"), "min_dur": 120}
]

start_time_minutes = time_to_minutes("9:00AM")
start_location = "Financial District"
max_meetings = 0
best_itinerary = None

for perm in itertools.permutations(meetings):
    current_time = start_time_minutes
    current_location = start_location
    itinerary = []
    for meeting in perm:
        travel_dur = travel_time[current_location][meeting["location"]]
        arrival = current_time + travel_dur
        start_meeting = max(arrival, meeting["avail_start"])
        end_meeting = start_meeting + meeting["min_dur"]
        if end_meeting <= meeting["avail_end"]:
            itinerary.append((meeting, start_meeting, end_meeting))
            current_time = end_meeting
            current_location = meeting["location"]
        else:
            continue
    if len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary
        if max_meetings == 5:
            break

if best_itinerary is None:
    result = {"itinerary": []}
else:
    result = {
        "itinerary": [
            {
                "action": "meet",
                "location": mtg["location"],
                "person": mtg["person"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            }
            for mtg, start, end in best_itinerary
        ]
    }

print(json.dumps(result))