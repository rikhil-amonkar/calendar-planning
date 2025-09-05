import json

# Convert minutes (since midnight) into H:MM format (24‐hour clock)
def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define the travel times as a nested dictionary.
travel_times = {
    "Union Square": {
        "Presidio": 24,
        "Alamo Square": 15,
        "Marina District": 18,
        "Financial District": 9,
        "Nob Hill": 9,
        "Sunset District": 27,
        "Chinatown": 7,
        "Russian Hill": 13,
        "North Beach": 10,
        "Haight-Ashbury": 18
    },
    "Presidio": {
        "Union Square": 22,
        "Alamo Square": 19,
        "Marina District": 11,
        "Financial District": 23,
        "Nob Hill": 18,
        "Sunset District": 15,
        "Chinatown": 21,
        "Russian Hill": 14,
        "North Beach": 18,
        "Haight-Ashbury": 15
    },
    "Alamo Square": {
        "Union Square": 14,
        "Presidio": 17,
        "Marina District": 15,
        "Financial District": 17,
        "Nob Hill": 11,
        "Sunset District": 16,
        "Chinatown": 15,
        "Russian Hill": 13,
        "North Beach": 15,
        "Haight-Ashbury": 5
    },
    "Marina District": {
        "Union Square": 16,
        "Presidio": 10,
        "Alamo Square": 15,
        "Financial District": 17,
        "Nob Hill": 12,
        "Sunset District": 19,
        "Chinatown": 15,
        "Russian Hill": 8,
        "North Beach": 11,
        "Haight-Ashbury": 16
    },
    "Financial District": {
        "Union Square": 9,
        "Presidio": 22,
        "Alamo Square": 17,
        "Marina District": 15,
        "Nob Hill": 8,
        "Sunset District": 30,
        "Chinatown": 5,
        "Russian Hill": 11,
        "North Beach": 7,
        "Haight-Ashbury": 19
    },
    "Nob Hill": {
        "Union Square": 7,
        "Presidio": 17,
        "Alamo Square": 11,
        "Marina District": 11,
        "Financial District": 9,
        "Sunset District": 24,
        "Chinatown": 6,
        "Russian Hill": 5,
        "North Beach": 8,
        "Haight-Ashbury": 13
    },
    "Sunset District": {
        "Union Square": 30,
        "Presidio": 16,
        "Alamo Square": 17,
        "Marina District": 21,
        "Financial District": 30,
        "Nob Hill": 27,
        "Chinatown": 30,
        "Russian Hill": 24,
        "North Beach": 28,
        "Haight-Ashbury": 15
    },
    "Chinatown": {
        "Union Square": 7,
        "Presidio": 19,
        "Alamo Square": 17,
        "Marina District": 12,
        "Financial District": 5,
        "Nob Hill": 9,
        "Sunset District": 29,
        "Russian Hill": 7,
        "North Beach": 3,
        "Haight-Ashbury": 19
    },
    "Russian Hill": {
        "Union Square": 10,
        "Presidio": 14,
        "Alamo Square": 15,
        "Marina District": 7,
        "Financial District": 11,
        "Nob Hill": 5,
        "Sunset District": 23,
        "Chinatown": 9,
        "North Beach": 5,
        "Haight-Ashbury": 17
    },
    "North Beach": {
        "Union Square": 7,
        "Presidio": 17,
        "Alamo Square": 16,
        "Marina District": 9,
        "Financial District": 8,
        "Nob Hill": 7,
        "Sunset District": 27,
        "Chinatown": 6,
        "Russian Hill": 4,
        "Haight-Ashbury": 18
    },
    "Haight-Ashbury": {
        "Union Square": 19,
        "Presidio": 15,
        "Alamo Square": 5,
        "Marina District": 17,
        "Financial District": 21,
        "Nob Hill": 15,
        "Sunset District": 15,
        "Chinatown": 19,
        "Russian Hill": 17,
        "North Beach": 19
    }
}

# Define the meeting constraints as a list of dictionaries.
# Times are stored in minutes from midnight.
meetings = [
    {
        "person": "Kimberly",
        "location": "Presidio",
        "window_start": 15 * 60 + 30,  # 15:30 -> 930
        "window_end": 16 * 60,         # 16:00 -> 960
        "duration": 15
    },
    {
        "person": "Elizabeth",
        "location": "Alamo Square",
        "window_start": 19 * 60 + 15,  # 19:15 -> 1155
        "window_end": 20 * 60 + 15,      # 20:15 -> 1215
        "duration": 15
    },
    {
        "person": "Joshua",
        "location": "Marina District",
        "window_start": 10 * 60 + 30,  # 10:30 -> 630
        "window_end": 14 * 60 + 15,      # 14:15 -> 855
        "duration": 45
    },
    {
        "person": "Sandra",
        "location": "Financial District",
        "window_start": 19 * 60 + 30,  # 19:30 -> 1170
        "window_end": 20 * 60 + 15,      # 20:15 -> 1215
        "duration": 45
    },
    {
        "person": "Kenneth",
        "location": "Nob Hill",
        "window_start": 12 * 60 + 45,  # 12:45 -> 765
        "window_end": 21 * 60 + 45,      # 21:45 -> 1305
        "duration": 30
    },
    {
        "person": "Betty",
        "location": "Sunset District",
        "window_start": 14 * 60,       # 14:00 -> 840
        "window_end": 19 * 60,         # 19:00 -> 1140
        "duration": 60
    },
    {
        "person": "Deborah",
        "location": "Chinatown",
        "window_start": 17 * 60 + 15,  # 17:15 -> 1035
        "window_end": 20 * 60 + 30,      # 20:30 -> 1230
        "duration": 15
    },
    {
        "person": "Barbara",
        "location": "Russian Hill",
        "window_start": 17 * 60 + 30,  # 17:30 -> 1050
        "window_end": 21 * 60 + 15,      # 21:15 -> 1275
        "duration": 120
    },
    {
        "person": "Steven",
        "location": "North Beach",
        "window_start": 17 * 60 + 45,  # 17:45 -> 1065
        "window_end": 20 * 60 + 45,      # 20:45 -> 1245
        "duration": 90
    },
    {
        "person": "Daniel",
        "location": "Haight-Ashbury",
        "window_start": 18 * 60 + 30,  # 18:30 -> 1110
        "window_end": 18 * 60 + 45,      # 18:45 -> 1125
        "duration": 15
    }
]

# Recursive backtracking search to build a feasible schedule that maximizes the number of meetings.
def find_schedule(current_location, current_time, remaining_meetings):
    best_schedule = []
    for i, meeting in enumerate(remaining_meetings):
        # Compute travel time from current location to the meeting location.
        travel = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel
        # The meeting cannot start before the travel and the meeting's available window
        meeting_start = max(arrival_time, meeting["window_start"])
        meeting_end = meeting_start + meeting["duration"]
        if meeting_end <= meeting["window_end"]:
            # This meeting is feasible. Create an entry.
            meeting_entry = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            # Create new remaining meetings list without the current one.
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            # Recurse from the new state.
            subsequent_schedule = find_schedule(meeting["location"], meeting_end, new_remaining)
            candidate_schedule = [meeting_entry] + subsequent_schedule
            if len(candidate_schedule) > len(best_schedule):
                best_schedule = candidate_schedule
    return best_schedule

def main():
    # Start at Union Square at 9:00 (9*60 = 540 minutes)
    start_location = "Union Square"
    start_time = 9 * 60
    optimal_schedule = find_schedule(start_location, start_time, meetings)
    # Output result as JSON-formatted dictionary.
    result = {"itinerary": optimal_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()