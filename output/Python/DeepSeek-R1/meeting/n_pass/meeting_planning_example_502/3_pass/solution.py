import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times as a nested dictionary
travel_times = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "North Beach": 7
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Pacific Heights": 16,
        "North Beach": 24
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "Pacific Heights": 10,
        "North Beach": 3
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "Pacific Heights": 15,
        "North Beach": 10
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "Pacific Heights": 12,
        "North Beach": 6
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "North Beach": 9
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    }
}

# Define friends in the order to meet them
friends = [
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "available_start": time_to_minutes("8:00"),
        "available_end": time_to_minutes("11:15"),
        "min_duration": 30
    },
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "available_start": time_to_minutes("11:00"),
        "available_end": time_to_minutes("15:00"),
        "min_duration": 105
    },
    {
        "name": "Karen",
        "location": "Chinatown",
        "available_start": time_to_minutes("13:45"),
        "available_end": time_to_minutes("16:30"),
        "min_duration": 15
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "available_start": time_to_minutes("14:30"),
        "available_end": time_to_minutes("20:45"),
        "min_duration": 120
    },
    {
        "name": "Brian",
        "location": "Union Square",
        "available_start": time_to_minutes("15:00"),
        "available_end": time_to_minutes("17:15"),
        "min_duration": 30
    }
]

# Starting point
current_location = "Financial District"
current_time = time_to_minutes("9:00")  # 9:00 AM

itinerary = []

# Process Rebecca
travel_time = travel_times[current_location][friends[0]["location"]]
current_time += travel_time
start_meeting = max(current_time, friends[0]["available_start"])
end_meeting = start_meeting + friends[0]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": friends[0]["location"],
    "person": friends[0]["name"],
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})
current_time = end_meeting
current_location = friends[0]["location"]

# Process Stephanie
travel_time = travel_times[current_location][friends[1]["location"]]
current_time += travel_time
start_meeting = max(current_time, friends[1]["available_start"])
end_meeting = start_meeting + friends[1]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": friends[1]["location"],
    "person": friends[1]["name"],
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})
current_time = end_meeting
current_location = friends[1]["location"]

# Process Karen
travel_time = travel_times[current_location][friends[2]["location"]]
current_time += travel_time
start_meeting = max(current_time, friends[2]["available_start"])
end_meeting = start_meeting + friends[2]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": friends[2]["location"],
    "person": friends[2]["name"],
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})
current_time = end_meeting
current_location = friends[2]["location"]

# Process Steven
travel_time = travel_times[current_location][friends[3]["location"]]
current_time += travel_time
start_meeting = max(current_time, friends[3]["available_start"])
end_meeting = start_meeting + friends[3]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": friends[3]["location"],
    "person": friends[3]["name"],
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})
current_time = end_meeting
current_location = friends[3]["location"]

# Process Brian
travel_time = travel_times[current_location][friends[4]["location"]]
current_time += travel_time
start_meeting = max(current_time, friends[4]["available_start"])
end_meeting = start_meeting + friends[4]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": friends[4]["location"],
    "person": friends[4]["name"],
    "start_time": minutes_to_time(start_meeting),
    "end_time": minutes_to_time(end_meeting)
})

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))