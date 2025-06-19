import itertools
import json

def time_str_to_minutes(s):
    if s.endswith('AM') or s.endswith('PM'):
        period = s[-2:]
        time_part = s[:-2].strip()
        if ':' in time_part:
            parts = time_part.split(':', 1)
            hour_str = parts[0]
            minute_str = parts[1]
        else:
            hour_str = time_part
            minute_str = "00"
        hour = int(hour_str)
        minute = int(minute_str)
        if period == 'PM' and hour != 12:
            hour += 12
        if period == 'AM' and hour == 12:
            hour = 0
        return hour * 60 + minute

travel_time = {
    "Alamo Square": {
        "Russian Hill": 13,
        "Presidio": 18,
        "Chinatown": 16,
        "Sunset District": 16,
        "The Castro": 8,
        "Embarcadero": 17,
        "Golden Gate Park": 9
    },
    "Russian Hill": {
        "Alamo Square": 15,
        "Presidio": 14,
        "Chinatown": 9,
        "Sunset District": 23,
        "The Castro": 21,
        "Embarcadero": 8,
        "Golden Gate Park": 21
    },
    "Presidio": {
        "Alamo Square": 18,
        "Russian Hill": 14,
        "Chinatown": 21,
        "Sunset District": 15,
        "The Castro": 21,
        "Embarcadero": 20,
        "Golden Gate Park": 12
    },
    "Chinatown": {
        "Alamo Square": 17,
        "Russian Hill": 7,
        "Presidio": 19,
        "Sunset District": 29,
        "The Castro": 22,
        "Embarcadero": 5,
        "Golden Gate Park": 23
    },
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Presidio": 16,
        "Chinatown": 30,
        "The Castro": 17,
        "Embarcadero": 31,
        "Golden Gate Park": 11
    },
    "The Castro": {
        "Alamo Square": 8,
        "Russian Hill": 18,
        "Presidio": 20,
        "Chinatown": 20,
        "Sunset District": 17,
        "Embarcadero": 22,
        "Golden Gate Park": 11
    },
    "Embarcadero": {
        "Alamo Square": 19,
        "Russian Hill": 8,
        "Presidio": 20,
        "Chinatown": 7,
        "Sunset District": 30,
        "The Castro": 25,
        "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Presidio": 11,
        "Chinatown": 23,
        "Sunset District": 10,
        "The Castro": 13,
        "Embarcadero": 25
    }
}

friends_list = [
    {
        "name": "Emily",
        "location": "Russian Hill",
        "window_start": time_str_to_minutes("12:15PM"),
        "window_end": time_str_to_minutes("2:15PM"),
        "min_duration": 105
    },
    {
        "name": "Mark",
        "location": "Presidio",
        "window_start": time_str_to_minutes("2:45PM"),
        "window_end": time_str_to_minutes("7:30PM"),
        "min_duration": 60
    },
    {
        "name": "Deborah",
        "location": "Chinatown",
        "window_start": time_str_to_minutes("7:30AM"),
        "window_end": time_str_to_minutes("3:30PM"),
        "min_duration": 45
    },
    {
        "name": "Margaret",
        "location": "Sunset District",
        "window_start": time_str_to_minutes("9:30PM"),
        "window_end": time_str_to_minutes("10:30PM"),
        "min_duration": 60
    },
    {
        "name": "George",
        "location": "The Castro",
        "window_start": time_str_to_minutes("7:30AM"),
        "window_end": time_str_to_minutes("2:15PM"),
        "min_duration": 60
    },
    {
        "name": "Andrew",
        "location": "Embarcadero",
        "window_start": time_str_to_minutes("8:15PM"),
        "window_end": time_str_to_minutes("10:00PM"),
        "min_duration": 75
    },
    {
        "name": "Steven",
        "location": "Golden Gate Park",
        "window_start": time_str_to_minutes("11:15AM"),
        "window_end": time_str_to_minutes("9:15PM"),
        "min_duration": 105
    }
]

n = len(friends_list)
found = False
result_itinerary = []

for k in range(n, 0, -1):
    for subset in itertools.combinations(friends_list, k):
        for perm in itertools.permutations(subset):
            current_time = 540
            current_location = "Alamo Square"
            schedule_for_perm = []
            feasible = True
            for friend in perm:
                if current_location == friend['location']:
                    travel_dur = 0
                else:
                    try:
                        travel_dur = travel_time[current_location][friend['location']]
                    except KeyError:
                        feasible = False
                        break
                arrival_time = current_time + travel_dur
                meeting_start = max(arrival_time, friend['window_start'])
                if meeting_start > friend['window_end']:
                    feasible = False
                    break
                meeting_end = meeting_start + friend['min_duration']
                if meeting_end > friend['window_end']:
                    feasible = False
                    break
                schedule_for_perm.append((friend, meeting_start, meeting_end))
                current_time = meeting_end
                current_location = friend['location']
            if feasible:
                itinerary = []
                for meeting in schedule_for_perm:
                    friend = meeting[0]
                    start_min = meeting[1]
                    end_min = meeting[2]
                    start_hour = start_min // 60
                    start_minute = start_min % 60
                    end_hour = end_min // 60
                    end_minute = end_min % 60
                    start_str = f"{start_hour}:{start_minute:02d}"
                    end_str = f"{end_hour}:{end_minute:02d}"
                    itinerary.append({
                        "action": "meet",
                        "location": friend['location'],
                        "person": friend['name'],
                        "start_time": start_str,
                        "end_time": end_str
                    })
                result_itinerary = itinerary
                found = True
                break
        if found:
            break
    if found:
        break

if found:
    result = {"itinerary": result_itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))