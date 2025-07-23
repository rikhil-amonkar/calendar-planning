import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Bayview": {"North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19, "Nob Hill": 20, "Golden Gate Park": 22, "Union Square": 18, "Alamo Square": 16, "Presidio": 32, "Chinatown": 19, "Pacific Heights": 23},
    "North Beach": {"Bayview": 25, "Fisherman's Wharf": 5, "Haight-Ashbury": 18, "Nob Hill": 7, "Golden Gate Park": 22, "Union Square": 7, "Alamo Square": 16, "Presidio": 17, "Chinatown": 6, "Pacific Heights": 8},
    "Fisherman's Wharf": {"Bayview": 26, "North Beach": 6, "Haight-Ashbury": 22, "Nob Hill": 11, "Golden Gate Park": 25, "Union Square": 13, "Alamo Square": 21, "Presidio": 17, "Chinatown": 12, "Pacific Heights": 12},
    "Haight-Ashbury": {"Bayview": 18, "North Beach": 19, "Fisherman's Wharf": 23, "Nob Hill": 15, "Golden Gate Park": 7, "Union Square": 19, "Alamo Square": 5, "Presidio": 15, "Chinatown": 19, "Pacific Heights": 12},
    "Nob Hill": {"Bayview": 19, "North Beach": 8, "Fisherman's Wharf": 10, "Haight-Ashbury": 13, "Golden Gate Park": 17, "Union Square": 7, "Alamo Square": 11, "Presidio": 17, "Chinatown": 6, "Pacific Heights": 8},
    "Golden Gate Park": {"Bayview": 23, "North Beach": 23, "Fisherman's Wharf": 24, "Haight-Ashbury": 7, "Nob Hill": 20, "Union Square": 22, "Alamo Square": 9, "Presidio": 11, "Chinatown": 23, "Pacific Heights": 16},
    "Union Square": {"Bayview": 15, "North Beach": 10, "Fisherman's Wharf": 15, "Haight-Ashbury": 18, "Nob Hill": 9, "Golden Gate Park": 22, "Alamo Square": 14, "Presidio": 24, "Chinatown": 7, "Pacific Heights": 15},
    "Alamo Square": {"Bayview": 16, "North Beach": 15, "Fisherman's Wharf": 19, "Haight-Ashbury": 5, "Nob Hill": 11, "Golden Gate Park": 9, "Union Square": 14, "Presidio": 17, "Chinatown": 15, "Pacific Heights": 10},
    "Presidio": {"Bayview": 31, "North Beach": 18, "Fisherman's Wharf": 19, "Haight-Ashbury": 15, "Nob Hill": 18, "Golden Gate Park": 12, "Union Square": 22, "Alamo Square": 19, "Chinatown": 21, "Pacific Heights": 11},
    "Chinatown": {"Bayview": 20, "North Beach": 3, "Fisherman's Wharf": 8, "Haight-Ashbury": 19, "Nob Hill": 9, "Golden Gate Park": 23, "Union Square": 7, "Alamo Square": 17, "Presidio": 19, "Pacific Heights": 10},
    "Pacific Heights": {"Bayview": 22, "North Beach": 9, "Fisherman's Wharf": 13, "Haight-Ashbury": 11, "Nob Hill": 8, "Golden Gate Park": 15, "Union Square": 12, "Alamo Square": 10, "Presidio": 11, "Chinatown": 11}
}

# Define meeting constraints
meetings = {
    "Brian": {"location": "North Beach", "start": "13:00", "end": "19:00", "min_duration": 90},
    "Richard": {"location": "Fisherman's Wharf", "start": "11:00", "end": "12:45", "min_duration": 60},
    "Ashley": {"location": "Haight-Ashbury", "start": "15:00", "end": "20:30", "min_duration": 90},
    "Elizabeth": {"location": "Nob Hill", "start": "11:45", "end": "18:30", "min_duration": 75},
    "Jessica": {"location": "Golden Gate Park", "start": "20:00", "end": "21:45", "min_duration": 105},
    "Deborah": {"location": "Union Square", "start": "17:30", "end": "22:00", "min_duration": 60},
    "Kimberly": {"location": "Alamo Square", "start": "17:30", "end": "21:15", "min_duration": 45},
    "Matthew": {"location": "Presidio", "start": "08:15", "end": "09:00", "min_duration": 15},
    "Kenneth": {"location": "Chinatown", "start": "13:45", "end": "19:30", "min_duration": 105},
    "Anthony": {"location": "Pacific Heights", "start": "14:15", "end": "16:00", "min_duration": 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start, end, min_duration, current_time):
    meeting_start = max(parse_time(start), current_time)
    meeting_end = min(parse_time(end), meeting_start + timedelta(minutes=min_duration))
    return meeting_start + timedelta(minutes=min_duration) <= parse_time(end)

def find_next_meeting(current_location, current_time, remaining_meetings):
    best_meeting = None
    best_travel_time = float('inf')
    
    for person, details in remaining_meetings.items():
        if can_meet(details["start"], details["end"], details["min_duration"], current_time):
            travel_time = travel_times[current_location][details["location"]]
            arrival_time = current_time + timedelta(minutes=travel_time)
            if arrival_time + timedelta(minutes=details["min_duration"]) <= parse_time(details["end"]):
                if travel_time < best_travel_time:
                    best_travel_time = travel_time
                    best_meeting = (person, details["location"], arrival_time)
    
    return best_meeting

def create_schedule():
    itinerary = []
    current_location = "Bayview"
    current_time = parse_time("09:00")
    remaining_meetings = meetings.copy()
    
    while remaining_meetings:
        next_meeting = find_next_meeting(current_location, current_time, remaining_meetings)
        if not next_meeting:
            break
        
        person, location, start_time = next_meeting
        details = remaining_meetings.pop(person)
        end_time = start_time + timedelta(minutes=details["min_duration"])
        
        # Ensure all meetings are within their availability
        if not can_meet(details["start"], details["end"], details["min_duration"], start_time):
            remaining_meetings[person] = details  # Put it back if it doesn't fit
            continue
        
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
        
        current_location = location
        current_time = end_time
    
    return {"itinerary": itinerary}

schedule = create_schedule()
print(json.dumps(schedule, indent=2))