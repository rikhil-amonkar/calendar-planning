import json

# Helper functions to convert time formats.
def time_to_minutes(t):
    # t format: "H:MM" in 24-hour clock
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times between locations (in minutes)
travel_times = {
    "Presidio": {
        "Marina District": 11,
        "The Castro": 21,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Alamo Square": 19,
        "Golden Gate Park": 12
    },
    "Marina District": {
        "Presidio": 10,
        "The Castro": 21,
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Pacific Heights": 7,
        "Mission District": 20,
        "Alamo Square": 15,
        "Golden Gate Park": 18
    },
    "The Castro": {
        "Presidio": 20,
        "Marina District": 21,
        "Fisherman's Wharf": 24,
        "Bayview": 19,
        "Pacific Heights": 16,
        "Mission District": 7,
        "Alamo Square": 8,
        "Golden Gate Park": 11
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Marina District": 9,
        "The Castro": 27,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Mission District": 22,
        "Alamo Square": 21,
        "Golden Gate Park": 25
    },
    "Bayview": {
        "Presidio": 32,
        "Marina District": 27,
        "The Castro": 19,
        "Fisherman's Wharf": 25,
        "Pacific Heights": 23,
        "Mission District": 13,
        "Alamo Square": 16,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Marina District": 6,
        "The Castro": 16,
        "Fisherman's Wharf": 13,
        "Bayview": 22,
        "Mission District": 15,
        "Alamo Square": 10,
        "Golden Gate Park": 15
    },
    "Mission District": {
        "Presidio": 25,
        "Marina District": 19,
        "The Castro": 7,
        "Fisherman's Wharf": 22,
        "Bayview": 14,
        "Pacific Heights": 16,
        "Alamo Square": 11,
        "Golden Gate Park": 17
    },
    "Alamo Square": {
        "Presidio": 17,
        "Marina District": 15,
        "The Castro": 8,
        "Fisherman's Wharf": 19,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Golden Gate Park": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Marina District": 16,
        "The Castro": 13,
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Mission District": 17,
        "Alamo Square": 9
    }
}

# Meeting constraints for each friend.
# Times are stored in minutes after midnight.
meetings = [
    {
        "person": "Amanda",
        "location": "Marina District",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("19:30"),
        "duration": 105
    },
    {
        "person": "Melissa",
        "location": "The Castro",
        "avail_start": time_to_minutes("9:30"),
        "avail_end": time_to_minutes("17:00"),
        "duration": 30
    },
    {
        "person": "Jeffrey",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("12:45"),
        "avail_end": time_to_minutes("18:45"),
        "duration": 120
    },
    {
        "person": "Matthew",
        "location": "Bayview",
        "avail_start": time_to_minutes("10:15"),
        "avail_end": time_to_minutes("13:15"),
        "duration": 30
    },
    {
        "person": "Nancy",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("17:00"),
        "avail_end": time_to_minutes("21:30"),
        "duration": 105
    },
    {
        "person": "Karen",
        "location": "Mission District",
        "avail_start": time_to_minutes("17:30"),
        "avail_end": time_to_minutes("20:30"),
        "duration": 105
    },
    {
        "person": "Robert",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("11:15"),
        "avail_end": time_to_minutes("17:30"),
        "duration": 120
    },
    {
        "person": "Joseph",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("8:30"),
        "avail_end": time_to_minutes("21:15"),
        "duration": 105
    }
]

# Global variables to track the best itinerary found.
best_itinerary = []
best_meetings_count = 0
best_finish_time = float('inf')

def dfs(current_location, current_time, remaining, itinerary):
    global best_itinerary, best_meetings_count, best_finish_time

    # Check if this itinerary is better (more meetings or same count but finishes earlier)
    if len(itinerary) > best_meetings_count or (len(itinerary) == best_meetings_count and current_time < best_finish_time):
        best_itinerary = itinerary.copy()
        best_meetings_count = len(itinerary)
        best_finish_time = current_time

    # Try each meeting not yet scheduled.
    for i, meeting in enumerate(remaining):
        # Compute travel time from current location to meeting location.
        travel = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel
        # The meeting can start not before the friend's available start.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if meeting ends within the friend's available window.
        if meeting_end <= meeting["avail_end"]:
            new_itinerary = itinerary.copy()
            new_itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(meeting["location"], meeting_end, new_remaining, new_itinerary)

if __name__ == "__main__":
    # Start at Presidio at 9:00 AM.
    start_location = "Presidio"
    start_time = time_to_minutes("9:00")
    
    # Begin DFS search for the best (most meetings) itinerary.
    dfs(start_location, start_time, meetings, [])
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))