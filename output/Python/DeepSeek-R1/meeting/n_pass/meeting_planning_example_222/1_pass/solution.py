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

# Define travel times
travel_times = {
    "Nob Hill": {"North Beach": 8, "Fisherman's Wharf": 11, "Bayview": 19},
    "North Beach": {"Nob Hill": 7, "Fisherman's Wharf": 5, "Bayview": 22},
    "Fisherman's Wharf": {"Nob Hill": 11, "North Beach": 6, "Bayview": 26},
    "Bayview": {"Nob Hill": 20, "North Beach": 21, "Fisherman's Wharf": 25}
}

# Define friends in order of meeting: Helen, Kimberly, Patricia
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

# Start at Nob Hill at 9:00 AM (540 minutes from midnight)
current_time = 540  # 9:00 AM
current_location = "Nob Hill"
itinerary = []

# Calculate Helen's meeting end time based on Kimberly's availability and travel
kimberly_avail_start = friends[1]["avail_start"]
travel_to_kim = travel_times["North Beach"]["Fisherman's Wharf"]
helen_end_time = kimberly_avail_start - travel_to_kim  # 985 minutes (16:25)

# Travel to Helen at North Beach
travel_time = travel_times[current_location][friends[0]["location"]]
current_time += travel_time  # 548 minutes (9:08 AM)
meeting_start_helen = current_time
meeting_end_helen = helen_end_time
# Add Helen's meeting to itinerary
itinerary.append({
    "action": "meet",
    "location": friends[0]["location"],
    "person": friends[0]["name"],
    "start_time": minutes_to_time(meeting_start_helen),
    "end_time": minutes_to_time(meeting_end_helen)
})

# Travel to Kimberly at Fisherman's Wharf
current_time = meeting_end_helen
current_location = friends[0]["location"]
travel_time = travel_times[current_location][friends[1]["location"]]
current_time += travel_time  # 990 minutes (16:30)
meeting_start_kim = current_time
meeting_end_kim = meeting_start_kim + friends[1]["min_duration"]  # 1035 minutes (17:15)
# Add Kimberly's meeting to itinerary
itinerary.append({
    "action": "meet",
    "location": friends[1]["location"],
    "person": friends[1]["name"],
    "start_time": minutes_to_time(meeting_start_kim),
    "end_time": minutes_to_time(meeting_end_kim)
})

# Travel to Patricia at Bayview
current_time = meeting_end_kim
current_location = friends[1]["location"]
travel_time = travel_times[current_location][friends[2]["location"]]
current_time += travel_time  # 1061 minutes (17:41)
meeting_start_pat = max(current_time, friends[2]["avail_start"])  # 1080 minutes (18:00)
meeting_end_pat = meeting_start_pat + friends[2]["min_duration"]  # 1200 minutes (20:00)
# Add Patricia's meeting to itinerary
itinerary.append({
    "action": "meet",
    "location": friends[2]["location"],
    "person": friends[2]["name"],
    "start_time": minutes_to_time(meeting_start_pat),
    "end_time": minutes_to_time(meeting_end_pat)
})

# Output the itinerary as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))