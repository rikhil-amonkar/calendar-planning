import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes_abs):
    hour = minutes_abs // 60
    minute = minutes_abs % 60
    return f"{hour}:{minute:02d}"

travel_times = {
    "Nob Hill": {"North Beach": 8, "Fisherman's Wharf": 11, "Bayview": 19},
    "North Beach": {"Nob Hill": 7, "Fisherman's Wharf": 5, "Bayview": 22},
    "Fisherman's Wharf": {"Nob Hill": 11, "North Beach": 6, "Bayview": 25},
    "Bayview": {"Nob Hill": 20, "North Beach": 21, "Fisherman's Wharf": 25}
}

friends = [
    {
        "name": "Helen",
        "location": "North Beach",
        "avail_start": time_to_minutes("7:00"),
        "avail_end": time_to_minutes("16:45"),
        "min_duration": 120
    },
    {
        "name": "Kimberly",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("16:30"),
        "avail_end": time_to_minutes("21:00"),
        "min_duration": 45
    },
    {
        "name": "Patricia",
        "location": "Bayview",
        "avail_start": time_to_minutes("18:00"),
        "avail_end": time_to_minutes("21:15"),
        "min_duration": 120
    }
]

current_time = 540
current_location = "Nob Hill"
itinerary = []

travel_to_helen = travel_times[current_location][friends[0]["location"]]
current_time += travel_to_helen
meeting_start_helen = current_time
meeting_end_helen = meeting_start_helen + friends[0]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": friends[0]["location"],
    "person": friends[0]["name"],
    "start_time": minutes_to_time(meeting_start_helen),
    "end_time": minutes_to_time(meeting_end_helen)
})

current_location = friends[0]["location"]
current_time = friends[1]["avail_start"] - travel_times[current_location][friends[1]["location"]]
travel_to_kim = travel_times[current_location][friends[1]["location"]]
current_time += travel_to_kim
meeting_start_kim = current_time
meeting_end_kim = meeting_start_kim + friends[1]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": friends[1]["location"],
    "person": friends[1]["name"],
    "start_time": minutes_to_time(meeting_start_kim),
    "end_time": minutes_to_time(meeting_end_kim)
})

current_location = friends[1]["location"]
travel_to_pat = travel_times[current_location][friends[2]["location"]]
current_time = meeting_end_kim + travel_to_pat
meeting_start_pat = max(current_time, friends[2]["avail_start"])
meeting_end_pat = meeting_start_pat + friends[2]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": friends[2]["location"],
    "person": friends[2]["name"],
    "start_time": minutes_to_time(meeting_start_pat),
    "end_time": minutes_to_time(meeting_end_pat)
})

result = {"itinerary": itinerary}
print(json.dumps(result))