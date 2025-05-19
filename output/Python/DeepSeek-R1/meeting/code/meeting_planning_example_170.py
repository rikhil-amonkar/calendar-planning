import json
from datetime import datetime, timedelta

def parse_time(s):
    return datetime.strptime(s, "%H:%M")

def format_time(dt):
    return f"{dt.hour}:{dt.minute:02d}"

travel_times = {
    'North Beach': {'Union Square': 7, 'Russian Hill': 4},
    'Union Square': {'North Beach': 10, 'Russian Hill': 13},
    'Russian Hill': {'North Beach': 5, 'Union Square': 11}
}

start_loc = 'North Beach'
start_time = parse_time('9:00')
current_time = start_time
current_loc = start_loc
itinerary = []

# Schedule Emily meeting
emily_loc = 'Union Square'
emily_start = parse_time('16:00')
emily_end = parse_time('17:15')
travel_duration = travel_times[current_loc][emily_loc]
departure = emily_start - timedelta(minutes=travel_duration)
if departure >= current_time:
    meet_emily_start = emily_start
    meet_emily_end = emily_end
    itinerary.append({
        "action": "meet",
        "location": emily_loc,
        "person": "Emily",
        "start_time": format_time(meet_emily_start),
        "end_time": format_time(meet_emily_end)
    })
    current_time = meet_emily_end
    current_loc = emily_loc

# Schedule Margaret meeting
margaret_loc = 'Russian Hill'
margaret_start = parse_time('19:00')
margaret_end = parse_time('21:00')
if current_loc != margaret_loc:
    travel_duration = travel_times[current_loc][margaret_loc]
    arrival = current_time + timedelta(minutes=travel_duration)
    if arrival <= margaret_start:
        meet_margaret_start = margaret_start
        meet_margaret_end = margaret_end
        itinerary.append({
            "action": "meet",
            "location": margaret_loc,
            "person": "Margaret",
            "start_time": format_time(meet_margaret_start),
            "end_time": format_time(meet_margaret_end)
        })

print(json.dumps({"itinerary": itinerary}, indent=2))