import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    "Russian Hill": {
        "Pacific Heights": 7, "North Beach": 5, "Golden Gate Park": 21, "Embarcadero": 8,
        "Haight-Ashbury": 17, "Fisherman's Wharf": 7, "Mission District": 16, "Alamo Square": 15,
        "Bayview": 23, "Richmond District": 14
    },
    "Pacific Heights": {
        "Russian Hill": 7, "North Beach": 9, "Golden Gate Park": 15, "Embarcadero": 10,
        "Haight-Ashbury": 11, "Fisherman's Wharf": 13, "Mission District": 15, "Alamo Square": 10,
        "Bayview": 22, "Richmond District": 12
    },
    "North Beach": {
        "Russian Hill": 4, "Pacific Heights": 8, "Golden Gate Park": 22, "Embarcadero": 6,
        "Haight-Ashbury": 18, "Fisherman's Wharf": 5, "Mission District": 18, "Alamo Square": 16,
        "Bayview": 25, "Richmond District": 18
    },
    "Golden Gate Park": {
        "Russian Hill": 19, "Pacific Heights": 16, "North Beach": 23, "Embarcadero": 25,
        "Haight-Ashbury": 7, "Fisherman's Wharf": 24, "Mission District": 17, "Alamo Square": 9,
        "Bayview": 23, "Richmond District": 7
    },
    "Embarcadero": {
        "Russian Hill": 8, "Pacific Heights": 11, "North Beach": 5, "Golden Gate Park": 25,
        "Haight-Ashbury": 21, "Fisherman's Wharf": 6, "Mission District": 20, "Alamo Square": 19,
        "Bayview": 21, "Richmond District": 21
    },
    "Haight-Ashbury": {
        "Russian Hill": 17, "Pacific Heights": 12, "North Beach": 19, "Golden Gate Park": 7,
        "Embarcadero": 20, "Fisherman's Wharf": 23, "Mission District": 11, "Alamo Square": 5,
        "Bayview": 18, "Richmond District": 10
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7, "Pacific Heights": 12, "North Beach": 6, "Golden Gate Park": 25,
        "Haight-Ashbury": 22, "Embarcadero": 8, "Mission District": 22, "Alamo Square": 21,
        "Bayview": 26, "Richmond District": 18
    },
    "Mission District": {
        "Russian Hill": 15, "Pacific Heights": 16, "North Beach": 17, "Golden Gate Park": 17,
        "Embarcadero": 19, "Haight-Ashbury": 12, "Fisherman's Wharf": 22, "Alamo Square": 11,
        "Bayview": 14, "Richmond District": 20
    },
    "Alamo Square": {
        "Russian Hill": 13, "Pacific Heights": 10, "North Beach": 15, "Golden Gate Park": 9,
        "Embarcadero": 16, "Haight-Ashbury": 5, "Fisherman's Wharf": 19, "Mission District": 10,
        "Bayview": 16, "Richmond District": 11
    },
    "Bayview": {
        "Russian Hill": 23, "Pacific Heights": 23, "North Beach": 22, "Golden Gate Park": 22,
        "Embarcadero": 19, "Haight-Ashbury": 19, "Fisherman's Wharf": 25, "Mission District": 13,
        "Alamo Square": 16, "Richmond District": 25
    },
    "Richmond District": {
        "Russian Hill": 13, "Pacific Heights": 10, "North Beach": 17, "Golden Gate Park": 9,
        "Embarcadero": 19, "Haight-Ashbury": 10, "Fisherman's Wharf": 18, "Mission District": 20,
        "Alamo Square": 13, "Bayview": 27
    }
}

# Define the meeting constraints
constraints = {
    "Emily": {"location": "Pacific Heights", "start": "9:15", "end": "13:45", "min_duration": 120},
    "Helen": {"location": "North Beach", "start": "13:45", "end": "18:45", "min_duration": 30},
    "Kimberly": {"location": "Golden Gate Park", "start": "18:45", "end": "21:15", "min_duration": 75},
    "James": {"location": "Embarcadero", "start": "10:30", "end": "11:30", "min_duration": 30},
    "Linda": {"location": "Haight-Ashbury", "start": "7:30", "end": "19:15", "min_duration": 15},
    "Paul": {"location": "Fisherman's Wharf", "start": "14:45", "end": "18:45", "min_duration": 90},
    "Anthony": {"location": "Mission District", "start": "8:00", "end": "14:45", "min_duration": 105},
    "Nancy": {"location": "Alamo Square", "start": "8:30", "end": "13:45", "min_duration": 120},
    "William": {"location": "Bayview", "start": "17:30", "end": "20:30", "min_duration": 120},
    "Margaret": {"location": "Richmond District", "start": "15:15", "end": "18:15", "min_duration": 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def find_optimal_schedule(constraints, travel_times):
    start_time = parse_time("9:00")
    current_location = "Russian Hill"
    itinerary = []

    def can_meet(start, end, min_duration):
        duration = (parse_time(end) - parse_time(start)).seconds // 60
        return duration >= min_duration

    def get_available_meetings(current_time, current_location):
        available_meetings = []
        for person, details in constraints.items():
            if details["location"] == current_location:
                if can_meet(details["start"], details["end"], details["min_duration"]):
                    start = max(parse_time(details["start"]), current_time)
                    end = parse_time(details["end"])
                    if (end - start).seconds // 60 >= details["min_duration"]:
                        available_meetings.append((person, start, end))
        return available_meetings

    while start_time < parse_time("21:15"):
        available_meetings = get_available_meetings(start_time, current_location)
        if available_meetings:
            available_meetings.sort(key=lambda x: x[1])
            person, start, end = available_meetings[0]
            itinerary.append({
                "action": "meet",
                "location": current_location,
                "person": person,
                "start_time": format_time(start),
                "end_time": format_time(end)
            })
            start_time = end
        else:
            next_meeting = None
            for person, details in constraints.items():
                if can_meet(details["start"], details["end"], details["min_duration"]):
                    travel_time = travel_times[current_location][details["location"]]
                    potential_start = parse_time(details["start"]) - timedelta(minutes=travel_time)
                    if potential_start > start_time:
                        if next_meeting is None or potential_start < next_meeting[0]:
                            next_meeting = (potential_start, details["location"])
            if next_meeting:
                travel_time = travel_times[current_location][next_meeting[1]]
                new_start_time = next_meeting[0] - timedelta(minutes=travel_time)
                itinerary.append({
                    "action": "travel",
                    "from": current_location,
                    "to": next_meeting[1],
                    "start_time": format_time(start_time),
                    "end_time": format_time(new_start_time)
                })
                start_time = new_start_time
                current_location = next_meeting[1]
            else:
                break

    return itinerary

itinerary = find_optimal_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))