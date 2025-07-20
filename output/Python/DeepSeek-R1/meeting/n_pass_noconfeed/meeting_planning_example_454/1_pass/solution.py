import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

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

def main():
    itinerary = []
    current_location = "Presidio"
    current_time = 9 * 60  # 9:00 AM

    # Travel to Mission District to meet Daniel
    travel = travel_times[current_location]["Mission District"]
    current_time += travel  # Arrive at 9:26
    start_meeting = current_time
    end_meeting = start_meeting + 105  # 11:11
    itinerary.append({
        "action": "meet",
        "location": "Mission District",
        "person": "Daniel",
        "start_time": minutes_to_time(start_meeting),
        "end_time": minutes_to_time(end_meeting)
    })
    current_time = end_meeting  # 11:11

    # Travel to Chinatown to meet Ronald
    travel = travel_times["Mission District"]["Chinatown"]
    current_time += travel  # Arrive at 11:27
    start_meeting = current_time
    end_meeting = start_meeting + 90  # 12:57
    itinerary.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "Ronald",
        "start_time": minutes_to_time(start_meeting),
        "end_time": minutes_to_time(end_meeting)
    })
    current_time = end_meeting  # 12:57

    # Travel to Golden Gate Park to meet Jessica
    travel = travel_times["Chinatown"]["Golden Gate Park"]
    current_time += travel  # Arrive at 13:20
    # Wait until Jessica's available time (13:45)
    if current_time < 13*60+45:
        current_time = 13*60+45
    start_meeting = current_time  # 13:45
    end_meeting = start_meeting + 30  # 14:15
    itinerary.append({
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Jessica",
        "start_time": minutes_to_time(start_meeting),
        "end_time": minutes_to_time(end_meeting)
    })
    current_time = end_meeting  # 14:15

    # Travel to North Beach to meet William
    travel = travel_times["Golden Gate Park"]["North Beach"]
    current_time += travel  # Arrive at 14:39
    start_meeting = current_time
    end_meeting = start_meeting + 15  # 14:54
    itinerary.append({
        "action": "meet",
        "location": "North Beach",
        "person": "William",
        "start_time": minutes_to_time(start_meeting),
        "end_time": minutes_to_time(end_meeting)
    })
    current_time = end_meeting  # 14:54

    # Travel to Bayview to meet Ashley
    travel = travel_times["North Beach"]["Bayview"]
    current_time += travel  # Arrive at 15:16
    # Wait until Ashley's available time (17:15)
    if current_time < 17*60+15:
        current_time = 17*60+15
    start_meeting = current_time  # 17:15
    end_meeting = start_meeting + 105  # 19:00
    itinerary.append({
        "action": "meet",
        "location": "Bayview",
        "person": "Ashley",
        "start_time": minutes_to_time(start_meeting),
        "end_time": minutes_to_time(end_meeting)
    })

    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()