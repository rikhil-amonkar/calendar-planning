#!/usr/bin/env python3
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define travel times between locations (in minutes)
travel_times = {
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Mission District"): 20,
    
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 25,
    
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Mission District"): 11,
    
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
}

# Define meeting constraints for each friend.
# Times are in minutes from midnight.
# 9:00 AM = 540, 9:45 = 585, 10:45 = 645, 11:00 = 660, etc.
meetings = [
    {"person": "Joshua", "location": "Embarcadero", "avail_start": 585, "avail_end": 1080, "duration":105},
    {"person": "Jeffrey", "location": "Bayview", "avail_start": 585, "avail_end": 1215, "duration":75},
    {"person": "Charles", "location": "Union Square", "avail_start": 645, "avail_end": 1215, "duration":120},
    {"person": "Joseph", "location": "Chinatown", "avail_start": 420, "avail_end": 930, "duration":60},
    # Elizabeth is omitted since her window (9:00-9:45) is unreachable from Marina starting at 9:00.
    {"person": "Matthew", "location": "Golden Gate Park", "avail_start": 660, "avail_end": 1170, "duration":45},
    {"person": "Carol", "location": "Financial District", "avail_start": 645, "avail_end": 675, "duration":15},
    {"person": "Paul", "location": "Haight-Ashbury", "avail_start": 1155, "avail_end": 1230, "duration":15},
    {"person": "Rebecca", "location": "Mission District", "avail_start": 1020, "avail_end": 1305, "duration":45},
]

def dfs(current_time, current_location, available_meetings, current_schedule):
    best_schedule = list(current_schedule)
    for i, meeting in enumerate(available_meetings):
        travel = travel_times.get((current_location, meeting["location"]))
        if travel is None:
            continue
        arrival = current_time + travel
        meeting_start = max(arrival, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        if meeting_end <= meeting["avail_end"]:
            meeting_event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            new_schedule = current_schedule + [meeting_event]
            new_available = available_meetings[:i] + available_meetings[i+1:]
            candidate_schedule = dfs(meeting_end, meeting["location"], new_available, new_schedule)
            if len(candidate_schedule) > len(best_schedule):
                best_schedule = candidate_schedule
    return best_schedule

def main():
    # Starting at Marina District at 9:00 AM (540 minutes)
    start_time = 540
    start_location = "Marina District"
    best_itinerary = dfs(start_time, start_location, meetings, [])
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()