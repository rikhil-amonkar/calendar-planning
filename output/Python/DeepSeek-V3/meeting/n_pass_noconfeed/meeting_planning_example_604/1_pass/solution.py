import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Locations
    locations = [
        "Fisherman's Wharf", "The Castro", "Golden Gate Park", "Embarcadero",
        "Russian Hill", "Nob Hill", "Alamo Square", "North Beach"
    ]
    
    # Travel times (in minutes)
    travel_times = {
        "Fisherman's Wharf": {
            "The Castro": 26, "Golden Gate Park": 25, "Embarcadero": 8,
            "Russian Hill": 7, "Nob Hill": 11, "Alamo Square": 20, "North Beach": 6
        },
        "The Castro": {
            "Fisherman's Wharf": 24, "Golden Gate Park": 11, "Embarcadero": 22,
            "Russian Hill": 18, "Nob Hill": 16, "Alamo Square": 8, "North Beach": 20
        },
        "Golden Gate Park": {
            "Fisherman's Wharf": 24, "The Castro": 13, "Embarcadero": 25,
            "Russian Hill": 19, "Nob Hill": 20, "Alamo Square": 10, "North Beach": 24
        },
        "Embarcadero": {
            "Fisherman's Wharf": 6, "The Castro": 25, "Golden Gate Park": 25,
            "Russian Hill": 8, "Nob Hill": 10, "Alamo Square": 19, "North Beach": 5
        },
        "Russian Hill": {
            "Fisherman's Wharf": 7, "The Castro": 21, "Golden Gate Park": 21,
            "Embarcadero": 8, "Nob Hill": 5, "Alamo Square": 15, "North Beach": 5
        },
        "Nob Hill": {
            "Fisherman's Wharf": 11, "The Castro": 17, "Golden Gate Park": 17,
            "Embarcadero": 9, "Russian Hill": 5, "Alamo Square": 11, "North Beach": 8
        },
        "Alamo Square": {
            "Fisherman's Wharf": 19, "The Castro": 8, "Golden Gate Park": 9,
            "Embarcadero": 17, "Russian Hill": 13, "Nob Hill": 11, "North Beach": 15
        },
        "North Beach": {
            "Fisherman's Wharf": 5, "The Castro": 22, "Golden Gate Park": 22,
            "Embarcadero": 6, "Russian Hill": 4, "Nob Hill": 7, "Alamo Square": 16
        }
    }

    # Friend constraints
    friends = [
        {"name": "Laura", "location": "The Castro", "start": "19:45", "end": "21:30", "duration": 105},
        {"name": "Daniel", "location": "Golden Gate Park", "start": "21:15", "end": "21:45", "duration": 15},
        {"name": "William", "location": "Embarcadero", "start": "7:00", "end": "9:00", "duration": 90},
        {"name": "Karen", "location": "Russian Hill", "start": "14:30", "end": "19:45", "duration": 30},
        {"name": "Stephanie", "location": "Nob Hill", "start": "7:30", "end": "9:30", "duration": 45},
        {"name": "Joseph", "location": "Alamo Square", "start": "11:30", "end": "12:45", "duration": 15},
        {"name": "Kimberly", "location": "North Beach", "start": "15:45", "end": "19:15", "duration": 30}
    ]

    # Filter out impossible meetings (duration > available time)
    possible_friends = [f for f in friends if (time_to_minutes(f["end"]) - time_to_minutes(f["start"]) >= f["duration"]]

    # Generate all possible permutations of meetings
    best_schedule = []
    max_meetings = 0

    for perm in permutations(possible_friends):
        current_location = "Fisherman's Wharf"
        current_time = time_to_minutes("9:00")
        schedule = []
        meetings = 0

        for friend in perm:
            travel_time = travel_times[current_location][friend["location"]]
            arrival_time = current_time + travel_time
            friend_start = time_to_minutes(friend["start"])
            friend_end = time_to_minutes(friend["end"])
            meeting_start = max(arrival_time, friend_start)
            meeting_end = meeting_start + friend["duration"]

            if meeting_end <= friend_end:
                schedule.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                })
                current_location = friend["location"]
                current_time = meeting_end
                meetings += 1

        if meetings > max_meetings:
            max_meetings = meetings
            best_schedule = schedule

    # Sort the best schedule by time
    best_schedule.sort(key=lambda x: time_to_minutes(x["start_time"]))

    return {"itinerary": best_schedule}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))