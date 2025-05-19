import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    "Bayview": {
        "North Beach": 22,
        "Fisherman's Wharf": 25,
        "Haight-Ashbury": 19,
        "Nob Hill": 20,
        "Golden Gate Park": 22,
        "Union Square": 18,
        "Alamo Square": 16,
        "Presidio": 32,
        "Chinatown": 19,
        "Pacific Heights": 23
    },
    "North Beach": {
        "Bayview": 25,
        "Fisherman's Wharf": 5,
        "Haight-Ashbury": 18,
        "Nob Hill": 7,
        "Golden Gate Park": 22,
        "Union Square": 7,
        "Alamo Square": 16,
        "Presidio": 17,
        "Chinatown": 6,
        "Pacific Heights": 8
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "North Beach": 6,
        "Haight-Ashbury": 22,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Union Square": 13,
        "Alamo Square": 21,
        "Presidio": 17,
        "Chinatown": 12,
        "Pacific Heights": 12
    },
    "Haight-Ashbury": {
        "Bayview": 18,
        "North Beach": 19,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Union Square": 19,
        "Alamo Square": 5,
        "Presidio": 15,
        "Chinatown": 19,
        "Pacific Heights": 12
    },
    "Nob Hill": {
        "Bayview": 19,
        "North Beach": 8,
        "Fisherman's Wharf": 10,
        "Haight-Ashbury": 13,
        "Golden Gate Park": 17,
        "Union Square": 7,
        "Alamo Square": 11,
        "Presidio": 17,
        "Chinatown": 6,
        "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Bayview": 23,
        "North Beach": 23,
        "Fisherman's Wharf": 24,
        "Haight-Ashbury": 7,
        "Nob Hill": 20,
        "Union Square": 22,
        "Alamo Square": 9,
        "Presidio": 11,
        "Chinatown": 23,
        "Pacific Heights": 16
    },
    "Union Square": {
        "Bayview": 15,
        "North Beach": 10,
        "Fisherman's Wharf": 15,
        "Haight-Ashbury": 18,
        "Nob Hill": 9,
        "Golden Gate Park": 22,
        "Alamo Square": 15,
        "Presidio": 24,
        "Chinatown": 7,
        "Pacific Heights": 15
    },
    "Alamo Square": {
        "Bayview": 16,
        "North Beach": 15,
        "Fisherman's Wharf": 19,
        "Haight-Ashbury": 5,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Union Square": 14,
        "Presidio": 17,
        "Chinatown": 15,
        "Pacific Heights": 10
    },
    "Presidio": {
        "Bayview": 31,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "Golden Gate Park": 12,
        "Union Square": 22,
        "Alamo Square": 19,
        "Chinatown": 21,
        "Pacific Heights": 11
    },
    "Chinatown": {
        "Bayview": 20,
        "North Beach": 3,
        "Fisherman's Wharf": 8,
        "Haight-Ashbury": 19,
        "Nob Hill": 9,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Alamo Square": 17,
        "Presidio": 19,
        "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Bayview": 22,
        "North Beach": 9,
        "Fisherman's Wharf": 13,
        "Haight-Ashbury": 11,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Union Square": 12,
        "Alamo Square": 10,
        "Presidio": 11,
        "Chinatown": 11
    }
}

# Meeting constraints
meetings = [
    {"person": "Matthew", "location": "Presidio", "start": "09:00", "end": "09:15", "duration": 15},
    {"person": "Richard", "location": "Fisherman's Wharf", "start": "11:00", "end": "12:45", "duration": 60},
    {"person": "Elizabeth", "location": "Nob Hill", "start": "11:45", "end": "18:30", "duration": 75},
    {"person": "Brian", "location": "North Beach", "start": "13:00", "end": "19:00", "duration": 90},
    {"person": "Anthony", "location": "Pacific Heights", "start": "14:15", "end": "16:00", "duration": 30},
    {"person": "Ashley", "location": "Haight-Ashbury", "start": "15:00", "end": "20:30", "duration": 90},
    {"person": "Deborah", "location": "Union Square", "start": "17:30", "end": "22:00", "duration": 60},
    {"person": "Kimberly", "location": "Alamo Square", "start": "17:30", "end": "21:15", "duration": 45},
    {"person": "Kenneth", "location": "Chinatown", "start": "13:45", "end": "19:30", "duration": 105},
    {"person": "Jessica", "location": "Golden Gate Park", "start": "20:00", "end": "21:45", "duration": 105}
]

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_dt):
    return time_dt.strftime('%H:%M')

# Start exploring the schedule
itinerary = []
current_time = parse_time("09:00")

def try_meeting(meeting, start_time):
    """Try to schedule a meeting and return the end time, or None if it can't be scheduled."""
    meeting_duration = timedelta(minutes=meeting["duration"])
    travel_time = travel_times["Bayview"][meeting["location"]]
    
    start_meeting_time = start_time + timedelta(minutes=travel_time)
    
    # Check if it fits in the meeting person's timeframe
    meeting_start_time = max(start_meeting_time, parse_time(meeting["start"]))
    meeting_end_time = meeting_start_time + meeting_duration
    
    if meeting_end_time <= parse_time(meeting["end"]):
        return meeting_end_time
    return None

# Schedule meetings considering constraints
for meeting in meetings:
    end_time = try_meeting(meeting, current_time)
    if end_time:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": format_time(end_time - timedelta(minutes=meeting["duration"])),
            "end_time": format_time(end_time)
        })
        current_time = end_time + timedelta(minutes=travel_times[meeting["location"]]["Bayview"])  # Return to Bayview

# Result in JSON format
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))