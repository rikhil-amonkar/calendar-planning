import itertools
import json

def time_to_minutes(time_str):
    s = time_str.replace(" ", "").upper()
    if s.endswith("AM") or s.endswith("PM"):
        meridian = s[-2:]
        time_part = s[:-2]
    else:
        meridian = None
        time_part = s
    parts = time_part.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    if meridian == "PM" and hour != 12:
        hour += 12
    elif meridian == "AM" and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 17
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15
    }
}

meetings = [
    {"person": "Helen", "location": "Golden Gate Park", "start_avail": time_to_minutes("9:30AM"), "end_avail": time_to_minutes("12:15PM"), "min_duration": 45},
    {"person": "Steven", "location": "The Castro", "start_avail": time_to_minutes("8:15PM"), "end_avail": time_to_minutes("10:00PM"), "min_duration": 105},
    {"person": "Deborah", "location": "Bayview", "start_avail": time_to_minutes("8:30AM"), "end_avail": time_to_minutes("12:00PM"), "min_duration": 30},
    {"person": "Matthew", "location": "Marina District", "start_avail": time_to_minutes("9:15AM"), "end_avail": time_to_minutes("2:15PM"), "min_duration": 45},
    {"person": "Joseph", "location": "Union Square", "start_avail": time_to_minutes("2:15PM"), "end_avail": time_to_minutes("6:45PM"), "min_duration": 120},
    {"person": "Ronald", "location": "Sunset District", "start_avail": time_to_minutes("4:00PM"), "end_avail": time_to_minutes("8:45PM"), "min_duration": 60},
    {"person": "Robert", "location": "Alamo Square", "start_avail": time_to_minutes("6:30PM"), "end_avail": time_to_minutes("9:15PM"), "min_duration": 120},
    {"person": "Rebecca", "location": "Financial District", "start_avail": time_to_minutes("2:45PM"), "end_avail": time_to_minutes("4:15PM"), "min_duration": 30},
    {"person": "Elizabeth", "location": "Mission District", "start_avail": time_to_minutes("6:30PM"), "end_avail": time_to_minutes("9:00PM"), "min_duration": 120}
]

start_time = 540
start_location = "Pacific Heights"
best_count = 0
best_schedule = None
total_meetings = len(meetings)

for perm in itertools.permutations(meetings):
    current_time = start_time
    current_loc = start_location
    schedule = []
    for meet in perm:
        travel = travel_times[current_loc][meet['location']]
        arrival = current_time + travel
        start_meet = max(arrival, meet['start_avail'])
        if start_meet + meet['min_duration'] <= meet['end_avail']:
            end_meet = start_meet + meet['min_duration']
            schedule.append({
                'meeting': meet,
                'start_time_min': start_meet,
                'end_time_min': end_meet
            })
            current_time = end_meet
            current_loc = meet['location']
    count = len(schedule)
    if count > best_count:
        best_count = count
        best_schedule = schedule
    if best_count == total_meetings:
        break

itinerary = []
if best_schedule is not None:
    for s in best_schedule:
        meet = s['meeting']
        itinerary.append({
            "action": "meet",
            "location": meet['location'],
            "person": meet['person'],
            "start_time": minutes_to_time(s['start_time_min']),
            "end_time": minutes_to_time(s['end_time_min'])
        })

result = {
    "itinerary": itinerary
}

print(json.dumps(result))