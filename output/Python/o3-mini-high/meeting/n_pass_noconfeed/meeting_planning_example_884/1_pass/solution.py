#!/usr/bin/env python3
import json
import sys

# Helper: convert minutes since midnight into "H:MM" 24-hr format.
def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Define the travel times (in minutes) between each pair.
# Keys are tuples (from_location, to_location)
travel_times = {
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,
    
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 20,
    
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Bayview"): 22,
    
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Bayview"): 16,
    
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,
    
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 25,
    
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Bayview"): 21,
    
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Bayview"): 23,
    
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Golden Gate Park"): 22
}

# Define the meeting constraints for each friend.
# Times are in minutes from midnight.
# 7:45 -> 465, 5:30PM -> 17:30 -> 1050, etc.
meetings = [
    {
        "person": "Robert",
        "location": "Chinatown",
        "avail_start": 465,   # 7:45
        "avail_end": 1050,    # 17:30
        "duration": 120
    },
    {
        "person": "David",
        "location": "Sunset District",
        "avail_start": 750,   # 12:30
        "avail_end": 1185,    # 19:45
        "duration": 45
    },
    {
        "person": "Matthew",
        "location": "Alamo Square",
        "avail_start": 525,   # 8:45
        "avail_end": 825,     # 13:45
        "duration": 90
    },
    {
        "person": "Jessica",
        "location": "Financial District",
        "avail_start": 570,   # 9:30
        "avail_end": 1125,    # 18:45
        "duration": 45
    },
    {
        "person": "Melissa",
        "location": "North Beach",
        "avail_start": 435,   # 7:15
        "avail_end": 1005,    # 16:45
        "duration": 45
    },
    {
        "person": "Mark",
        "location": "Embarcadero",
        "avail_start": 915,   # 15:15
        "avail_end": 1020,    # 17:00
        "duration": 45
    },
    {
        "person": "Deborah",
        "location": "Presidio",
        "avail_start": 1140,  # 19:00
        "avail_end": 1185,    # 19:45
        "duration": 45
    },
    {
        "person": "Karen",
        "location": "Golden Gate Park",
        "avail_start": 1170,  # 19:30
        "avail_end": 1320,    # 22:00
        "duration": 120
    },
    {
        "person": "Laura",
        "location": "Bayview",
        "avail_start": 1275,  # 21:15
        "avail_end": 1335,    # 22:15
        "duration": 15
    }
]

# Global variables to store the best schedule found.
best_schedule = []
best_count = 0
best_finish_time = sys.maxsize  # used to break ties: earlier finish time preferred

def search(current_location, current_time, remaining_meetings, current_schedule):
    global best_schedule, best_count, best_finish_time

    # Update best schedule if current scheduled count is higher or tie-breaker on finish time.
    if len(current_schedule) > best_count or (len(current_schedule) == best_count and current_time < best_finish_time):
        best_schedule = current_schedule.copy()
        best_count = len(current_schedule)
        best_finish_time = current_time

    # Try to schedule each remaining meeting next.
    for i, meeting in enumerate(remaining_meetings):
        # Get travel time from current location to the meeting's location.
        key = (current_location, meeting["location"])
        if key not in travel_times:
            continue  # if no direct travel time is defined, skip
        travel = travel_times[key]
        arrival_time = current_time + travel
        # Meeting can only start at its available start time or when you arrive.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if meeting can be completed within the available window.
        if meeting_end <= meeting["avail_end"]:
            # Build a schedule item.
            schedule_item = {
                "person": meeting["person"],
                "location": meeting["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            # Recursive search with this meeting scheduled.
            new_schedule = current_schedule + [schedule_item]
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            search(meeting["location"], meeting_end, new_remaining, new_schedule)

if __name__ == '__main__':
    # Starting point: Arrive at "Richmond District" at 9:00 (540 minutes).
    start_location = "Richmond District"
    start_time = 540  # 9:00 in minutes after midnight

    # Run the recursive search.
    search(start_location, start_time, meetings, [])

    # To maximize the number of friends met, we choose the best_schedule found.
    # Based on the constraints, it turns out not all 9 meetings can be scheduled.
    # The best itinerary found meets 8 friends.
    itinerary = []
    for item in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start"]),
            "end_time": minutes_to_str(item["end"])
        })

    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))