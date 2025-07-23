import json
from itertools import permutations

# Locations
locations = [
    "Bayview", "North Beach", "Fisherman's Wharf", "Haight-Ashbury", "Nob Hill",
    "Golden Gate Park", "Union Square", "Alamo Square", "Presidio", "Chinatown", "Pacific Heights"
]

# Travel times (in minutes) as a dictionary of dictionaries
travel_times = {
    "Bayview": {
        "North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19, "Nob Hill": 20,
        "Golden Gate Park": 22, "Union Square": 18, "Alamo Square": 16, "Presidio": 32,
        "Chinatown": 19, "Pacific Heights": 23
    },
    "North Beach": {
        "Bayview": 25, "Fisherman's Wharf": 5, "Haight-Ashbury": 18, "Nob Hill": 7,
        "Golden Gate Park": 22, "Union Square": 7, "Alamo Square": 16, "Presidio": 17,
        "Chinatown": 6, "Pacific Heights": 8
    },
    "Fisherman's Wharf": {
        "Bayview": 26, "North Beach": 6, "Haight-Ashbury": 22, "Nob Hill": 11,
        "Golden Gate Park": 25, "Union Square": 13, "Alamo Square": 21, "Presidio": 17,
        "Chinatown": 12, "Pacific Heights": 12
    },
    "Haight-Ashbury": {
        "Bayview": 18, "North Beach": 19, "Fisherman's Wharf": 23, "Nob Hill": 15,
        "Golden Gate Park": 7, "Union Square": 19, "Alamo Square": 5, "Presidio": 15,
        "Chinatown": 19, "Pacific Heights": 12
    },
    "Nob Hill": {
        "Bayview": 19, "North Beach": 8, "Fisherman's Wharf": 10, "Haight-Ashbury": 13,
        "Golden Gate Park": 17, "Union Square": 7, "Alamo Square": 11, "Presidio": 17,
        "Chinatown": 6, "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Bayview": 23, "North Beach": 23, "Fisherman's Wharf": 24, "Haight-Ashbury": 7,
        "Nob Hill": 20, "Union Square": 22, "Alamo Square": 9, "Presidio": 11,
        "Chinatown": 23, "Pacific Heights": 16
    },
    "Union Square": {
        "Bayview": 15, "North Beach": 10, "Fisherman's Wharf": 15, "Haight-Ashbury": 18,
        "Nob Hill": 9, "Golden Gate Park": 22, "Alamo Square": 15, "Presidio": 24,
        "Chinatown": 7, "Pacific Heights": 15
    },
    "Alamo Square": {
        "Bayview": 16, "North Beach": 15, "Fisherman's Wharf": 19, "Haight-Ashbury": 5,
        "Nob Hill": 11, "Golden Gate Park": 9, "Union Square": 14, "Presidio": 17,
        "Chinatown": 15, "Pacific Heights": 10
    },
    "Presidio": {
        "Bayview": 31, "North Beach": 18, "Fisherman's Wharf": 19, "Haight-Ashbury": 15,
        "Nob Hill": 18, "Golden Gate Park": 12, "Union Square": 22, "Alamo Square": 19,
        "Chinatown": 21, "Pacific Heights": 11
    },
    "Chinatown": {
        "Bayview": 20, "North Beach": 3, "Fisherman's Wharf": 8, "Haight-Ashbury": 19,
        "Nob Hill": 9, "Golden Gate Park": 23, "Union Square": 7, "Alamo Square": 17,
        "Presidio": 19, "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Bayview": 22, "North Beach": 9, "Fisherman's Wharf": 13, "Haight-Ashbury": 11,
        "Nob Hill": 8, "Golden Gate Park": 15, "Union Square": 12, "Alamo Square": 10,
        "Presidio": 11, "Chinatown": 11
    }
}

# Friends' availability and constraints
friends = [
    {"name": "Brian", "location": "North Beach", "start": 13.0, "end": 19.0, "duration": 1.5},
    {"name": "Richard", "location": "Fisherman's Wharf", "start": 11.0, "end": 12.75, "duration": 1.0},
    {"name": "Ashley", "location": "Haight-Ashbury", "start": 15.0, "end": 20.5, "duration": 1.5},
    {"name": "Elizabeth", "location": "Nob Hill", "start": 11.75, "end": 18.5, "duration": 1.25},
    {"name": "Jessica", "location": "Golden Gate Park", "start": 20.0, "end": 21.75, "duration": 1.75},
    {"name": "Deborah", "location": "Union Square", "start": 17.5, "end": 22.0, "duration": 1.0},
    {"name": "Kimberly", "location": "Alamo Square", "start": 17.5, "end": 21.25, "duration": 0.75},
    {"name": "Matthew", "location": "Presidio", "start": 8.25, "end": 9.0, "duration": 0.25},
    {"name": "Kenneth", "location": "Chinatown", "start": 13.75, "end": 19.5, "duration": 1.75},
    {"name": "Anthony", "location": "Pacific Heights", "start": 14.25, "end": 16.0, "duration": 0.5}
]

def time_to_minutes(time):
    hours = int(time)
    minutes = int((time - hours) * 60)
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def can_schedule(meeting1, meeting2, travel_time):
    start1, end1 = meeting1["start"], meeting1["end"]
    start2, end2 = meeting2["start"], meeting2["end"]
    return end1 + travel_time <= start2 or end2 + travel_time <= start1

def find_best_schedule():
    current_location = "Bayview"
    current_time = 9.0 * 60  # 9:00 AM in minutes
    itinerary = []
    remaining_friends = friends.copy()
    
    # First, meet Matthew if possible
    matthew = next((f for f in remaining_friends if f["name"] == "Matthew"), None)
    if matthew:
        travel_time = travel_times[current_location][matthew["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(matthew["start"]))
        meeting_end = meeting_start + int(matthew["duration"] * 60)
        if meeting_end <= time_to_minutes(matthew["end"]):
            itinerary.append({
                "action": "meet",
                "location": matthew["location"],
                "person": matthew["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = matthew["location"]
            current_time = meeting_end
            remaining_friends.remove(matthew)
    
    # Then meet Richard if possible
    richard = next((f for f in remaining_friends if f["name"] == "Richard"), None)
    if richard:
        travel_time = travel_times[current_location][richard["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(richard["start"]))
        meeting_end = meeting_start + int(richard["duration"] * 60)
        if meeting_end <= time_to_minutes(richard["end"]):
            itinerary.append({
                "action": "meet",
                "location": richard["location"],
                "person": richard["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = richard["location"]
            current_time = meeting_end
            remaining_friends.remove(richard)
    
    # Then meet Elizabeth if possible
    elizabeth = next((f for f in remaining_friends if f["name"] == "Elizabeth"), None)
    if elizabeth:
        travel_time = travel_times[current_location][elizabeth["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(elizabeth["start"]))
        meeting_end = meeting_start + int(elizabeth["duration"] * 60)
        if meeting_end <= time_to_minutes(elizabeth["end"]):
            itinerary.append({
                "action": "meet",
                "location": elizabeth["location"],
                "person": elizabeth["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = elizabeth["location"]
            current_time = meeting_end
            remaining_friends.remove(elizabeth)
    
    # Then meet Anthony if possible
    anthony = next((f for f in remaining_friends if f["name"] == "Anthony"), None)
    if anthony:
        travel_time = travel_times[current_location][anthony["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(anthony["start"]))
        meeting_end = meeting_start + int(anthony["duration"] * 60)
        if meeting_end <= time_to_minutes(anthony["end"]):
            itinerary.append({
                "action": "meet",
                "location": anthony["location"],
                "person": anthony["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = anthony["location"]
            current_time = meeting_end
            remaining_friends.remove(anthony)
    
    # Then meet Kenneth if possible
    kenneth = next((f for f in remaining_friends if f["name"] == "Kenneth"), None)
    if kenneth:
        travel_time = travel_times[current_location][kenneth["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(kenneth["start"]))
        meeting_end = meeting_start + int(kenneth["duration"] * 60)
        if meeting_end <= time_to_minutes(kenneth["end"]):
            itinerary.append({
                "action": "meet",
                "location": kenneth["location"],
                "person": kenneth["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = kenneth["location"]
            current_time = meeting_end
            remaining_friends.remove(kenneth)
    
    # Then meet Brian if possible
    brian = next((f for f in remaining_friends if f["name"] == "Brian"), None)
    if brian:
        travel_time = travel_times[current_location][brian["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(brian["start"]))
        meeting_end = meeting_start + int(brian["duration"] * 60)
        if meeting_end <= time_to_minutes(brian["end"]):
            itinerary.append({
                "action": "meet",
                "location": brian["location"],
                "person": brian["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = brian["location"]
            current_time = meeting_end
            remaining_friends.remove(brian)
    
    # Then meet Ashley if possible
    ashley = next((f for f in remaining_friends if f["name"] == "Ashley"), None)
    if ashley:
        travel_time = travel_times[current_location][ashley["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(ashley["start"]))
        meeting_end = meeting_start + int(ashley["duration"] * 60)
        if meeting_end <= time_to_minutes(ashley["end"]):
            itinerary.append({
                "action": "meet",
                "location": ashley["location"],
                "person": ashley["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = ashley["location"]
            current_time = meeting_end
            remaining_friends.remove(ashley)
    
    # Then meet Kimberly if possible
    kimberly = next((f for f in remaining_friends if f["name"] == "Kimberly"), None)
    if kimberly:
        travel_time = travel_times[current_location][kimberly["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(kimberly["start"]))
        meeting_end = meeting_start + int(kimberly["duration"] * 60)
        if meeting_end <= time_to_minutes(kimberly["end"]):
            itinerary.append({
                "action": "meet",
                "location": kimberly["location"],
                "person": kimberly["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = kimberly["location"]
            current_time = meeting_end
            remaining_friends.remove(kimberly)
    
    # Then meet Deborah if possible
    deborah = next((f for f in remaining_friends if f["name"] == "Deborah"), None)
    if deborah:
        travel_time = travel_times[current_location][deborah["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(deborah["start"]))
        meeting_end = meeting_start + int(deborah["duration"] * 60)
        if meeting_end <= time_to_minutes(deborah["end"]):
            itinerary.append({
                "action": "meet",
                "location": deborah["location"],
                "person": deborah["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = deborah["location"]
            current_time = meeting_end
            remaining_friends.remove(deborah)
    
    # Finally, meet Jessica if possible
    jessica = next((f for f in remaining_friends if f["name"] == "Jessica"), None)
    if jessica:
        travel_time = travel_times[current_location][jessica["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(jessica["start"]))
        meeting_end = meeting_start + int(jessica["duration"] * 60)
        if meeting_end <= time_to_minutes(jessica["end"]):
            itinerary.append({
                "action": "meet",
                "location": jessica["location"],
                "person": jessica["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
    
    return itinerary

def main():
    itinerary = find_best_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()