import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Travel times in minutes between locations (directed)
travel_times = {
    "Union Square": {
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Russian Hill": 13,
        "Marina District": 18,
        "North Beach": 10,
        "Chinatown": 7,
        "Pacific Heights": 15,
        "The Castro": 17,
        "Nob Hill": 9,
        "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Russian Hill": 15,
        "Marina District": 19,
        "North Beach": 17,
        "Chinatown": 16,
        "Pacific Heights": 16,
        "The Castro": 7,
        "Nob Hill": 12,
        "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "Mission District": 22,
        "Russian Hill": 7,
        "Marina District": 9,
        "North Beach": 6,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "The Castro": 27,
        "Nob Hill": 11,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Marina District": 7,
        "North Beach": 5,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "The Castro": 21,
        "Nob Hill": 5,
        "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16,
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Pacific Heights": 7,
        "The Castro": 22,
        "Nob Hill": 12,
        "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7,
        "Mission District": 18,
        "Fisherman's Wharf": 5,
        "Russian Hill": 4,
        "Marina District": 9,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 23,
        "Nob Hill": 7,
        "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7,
        "Mission District": 17,
        "Fisherman's Wharf": 8,
        "Russian Hill": 7,
        "Marina District": 12,
        "North Beach": 3,
        "Pacific Heights": 10,
        "The Castro": 22,
        "Nob Hill": 9,
        "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12,
        "Mission District": 15,
        "Fisherman's Wharf": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "North Beach": 9,
        "Chinatown": 11,
        "The Castro": 16,
        "Nob Hill": 8,
        "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19,
        "Mission District": 7,
        "Fisherman's Wharf": 24,
        "Russian Hill": 18,
        "Marina District": 21,
        "North Beach": 20,
        "Chinatown": 22,
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7,
        "Mission District": 13,
        "Fisherman's Wharf": 10,
        "Russian Hill": 5,
        "Marina District": 11,
        "North Beach": 8,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 17,
        "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Russian Hill": 24,
        "Marina District": 21,
        "North Beach": 28,
        "Chinatown": 30,
        "Pacific Heights": 21,
        "The Castro": 17,
        "Nob Hill": 27
    }
}

# Meeting constraints with available times (in minutes since midnight) and minimum meeting durations (in minutes)
meetings = [
    {"person": "Kevin", "location": "Mission District", "avail_start": 1245, "avail_end": 1305, "min_duration": 60},
    {"person": "Mark", "location": "Fisherman's Wharf", "avail_start": 1035, "avail_end": 1200, "min_duration": 90},
    {"person": "Jessica", "location": "Russian Hill", "avail_start": 540,  "avail_end": 900,  "min_duration": 120},
    {"person": "Jason", "location": "Marina District", "avail_start": 915,  "avail_end": 1305, "min_duration": 120},
    {"person": "John", "location": "North Beach", "avail_start": 585,  "avail_end": 1080, "min_duration": 15},
    {"person": "Karen", "location": "Chinatown", "avail_start": 1005, "avail_end": 1140, "min_duration": 75},
    {"person": "Sarah", "location": "Pacific Heights", "avail_start": 1050, "avail_end": 1095, "min_duration": 45},
    {"person": "Amanda", "location": "The Castro", "avail_start": 1200, "avail_end": 1275, "min_duration": 60},
    {"person": "Nancy", "location": "Nob Hill", "avail_start": 585,  "avail_end": 780,  "min_duration": 45},
    {"person": "Rebecca", "location": "Sunset District", "avail_start": 525,  "avail_end": 900,  "min_duration": 75}
]

# Global variable to hold the best (i.e. maximum count) itinerary found.
best_schedule = []

def search(current_time, current_location, visited, schedule):
    global best_schedule
    # Update best schedule if current schedule has more meetings
    if len(schedule) > len(best_schedule):
        best_schedule = schedule.copy()

    for meeting in meetings:
        if meeting["person"] in visited:
            continue

        # Get travel time from current location to the meeting location.
        if current_location in travel_times and meeting["location"] in travel_times[current_location]:
            travel_time = travel_times[current_location][meeting["location"]]
        else:
            continue

        arrival_time = current_time + travel_time
        # Wait if you arrive before the meeting's available start
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]

        # Check if we can finish the meeting before the person's available end time.
        if meeting_end <= meeting["avail_end"]:
            event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_schedule = schedule + [event]
            new_visited = visited | {meeting["person"]}
            search(meeting_end, meeting["location"], new_visited, new_schedule)

def main():
    # You arrive at Union Square at 9:00 AM (540 minutes after midnight)
    start_time = 540
    start_location = "Union Square"
    search(start_time, start_location, set(), [])
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()