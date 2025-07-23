import json
from itertools import permutations
from collections import namedtuple

def time_to_min(time_str):
    time_str = time_str.strip()
    meridian = None
    if time_str.endswith("AM") or time_str.endswith("PM"):
        meridian = time_str[-2:]
        time_part = time_str[:-2].strip()
    else:
        time_part = time_str
    parts = time_part.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    if meridian == "PM" and hour != 12:
        hour += 12
    if meridian == "AM" and hour == 12:
        hour = 0
    return hour * 60 + minute

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Haight-Ashbury"): 18,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19
}

Friend = namedtuple('Friend', ['name', 'location', 'available_start', 'available_end', 'min_duration'])

non_fixed_friends = [
    Friend("Joshua", "Marina District", time_to_min("10:30AM"), time_to_min("2:15PM"), 45),
    Friend("Kenneth", "Nob Hill", time_to_min("12:45PM"), time_to_min("9:45PM"), 30),
    Friend("Betty", "Sunset District", time_to_min("2:00PM"), time_to_min("7:00PM"), 60),
    Friend("Kimberly", "Presidio", time_to_min("3:30PM"), time_to_min("4:00PM"), 15),
    Friend("Deborah", "Chinatown", time_to_min("5:15PM"), time_to_min("8:30PM"), 15)
]

daniel = Friend("Daniel", "Haight-Ashbury", time_to_min("6:30PM"), time_to_min("6:45PM"), 15)
sandra = Friend("Sandra", "Financial District", time_to_min("7:30PM"), time_to_min("8:15PM"), 45)

start_time = time_to_min("9:00AM")
start_location = "Union Square"

found = False
result_itinerary = None

for r in range(len(non_fixed_friends), 0, -1):
    for perm in permutations(non_fixed_friends, r):
        current_time = start_time
        current_location = start_location
        scheduled = []
        valid_schedule = True
        for friend in perm:
            travel_key = (current_location, friend.location)
            if travel_key not in travel_times:
                valid_schedule = False
                break
            tt = travel_times[travel_key]
            arrival_time = current_time + tt
            start_meeting = max(arrival_time, friend.available_start)
            end_meeting = start_meeting + friend.min_duration
            if end_meeting > friend.available_end:
                valid_schedule = False
                break
            scheduled.append((friend, start_meeting, end_meeting))
            current_time = end_meeting
            current_location = friend.location
        
        if not valid_schedule:
            continue
        
        travel_key_daniel = (current_location, daniel.location)
        if travel_key_daniel not in travel_times:
            continue
        travel_time_daniel = travel_times[travel_key_daniel]
        arrival_daniel = current_time + travel_time_daniel
        if arrival_daniel > daniel.available_start:
            continue
        
        travel_key_sandra = (daniel.location, sandra.location)
        if travel_key_sandra not in travel_times:
            continue
        travel_time_sandra = travel_times[travel_key_sandra]
        start_sandra = sandra.available_start
        arrival_sandra = daniel.available_end + travel_time_sandra
        if arrival_sandra > start_sandra:
            continue
        
        itinerary_list = []
        for (friend, start_meeting, end_meeting) in scheduled:
            itinerary_list.append({
                "action": "meet",
                "location": friend.location,
                "person": friend.name,
                "start_time": min_to_time(start_meeting),
                "end_time": min_to_time(end_meeting)
            })
        itinerary_list.append({
            "action": "meet",
            "location": daniel.location,
            "person": daniel.name,
            "start_time": min_to_time(daniel.available_start),
            "end_time": min_to_time(daniel.available_end)
        })
        itinerary_list.append({
            "action": "meet",
            "location": sandra.location,
            "person": sandra.name,
            "start_time": min_to_time(sandra.available_start),
            "end_time": min_to_time(sandra.available_end)
        })
        
        result = {"itinerary": itinerary_list}
        found = True
        print(json.dumps(result))
        exit(0)

if not found:
    print(json.dumps({"itinerary": []}))