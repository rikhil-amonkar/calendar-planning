#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper functions for time arithmetic.
def minutes_to_time_str(total_minutes):
    # total_minutes is minutes from midnight
    hours = total_minutes // 60
    minutes = total_minutes % 60
    # Format as H:MM using 24-hour time (no leading zero for hour)
    return f"{hours}:{minutes:02d}"

def add_minutes(time_in_minutes, mins):
    return time_in_minutes + mins

# Define the meeting windows and minimum durations (in minutes)
# Times are expressed as minutes from midnight.
# 9:00 is 9*60 = 540.
# Meeting windows (start, end) and required durations:
# Joshua at Marina District: window 10:30 (630) to 14:15 (855), duration 45
# Kenneth at Nob Hill: window 12:45 (765) to 21:45 (1305), duration 30
# Betty at Sunset District: window 14:00 (840) to 19:00 (1140), duration 60
# Kimberly at Presidio: window 15:30 (930) to 16:00 (960), duration 15
# Deborah at Chinatown: window 17:15 (1035) to 20:30 (1230), duration 15
# Steven at North Beach: window 17:45 (1065) to 20:45 (1245), duration 90
# Sandra at Financial District: window 19:30 (1170) to 20:15 (1215), duration 45
# (Other friends exist but due to time window conflicts, we choose the optimal subset that maximizes number of meetings)
meeting_info = {
    "Joshua": {"location": "Marina District", "window_start": 630, "window_end": 855, "duration": 45},
    "Kenneth": {"location": "Nob Hill", "window_start": 765, "window_end": 1305, "duration": 30},
    "Betty": {"location": "Sunset District", "window_start": 840, "window_end": 1140, "duration": 60},
    "Kimberly": {"location": "Presidio", "window_start": 930, "window_end": 960, "duration": 15},
    "Deborah": {"location": "Chinatown", "window_start": 1035, "window_end": 1230, "duration": 15},
    "Steven": {"location": "North Beach", "window_start": 1065, "window_end": 1245, "duration": 90},
    "Sandra": {"location": "Financial District", "window_start": 1170, "window_end": 1215, "duration": 45},
}

# Define travel times between locations (in minutes)
# We'll use the given travel times as a dictionary where key is a tuple (from, to)
travel_times = {
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Haight-Ashbury"): 18,

    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,

    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,

    ("Marina District", "Union Square"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Haight-Ashbury"): 16,

    ("Financial District", "Union Square"): 9,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Haight-Ashbury"): 19,

    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,

    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Haight-Ashbury"): 15,

    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Haight-Ashbury"): 19,

    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Haight-Ashbury"): 17,

    ("North Beach", "Union Square"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Haight-Ashbury"): 18,

    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
}

# Our plan:
# Start at Union Square at 9:00 (540 minutes)
# 1. Go to Marina District for Joshua.
# 2. Then to Nob Hill for Kenneth.
# 3. Then to Sunset District for Betty.
# 4. Then to Presidio for Kimberly.
# 5. In the evening, from Presidio go to Chinatown for Deborah.
# 6. Then to North Beach for Steven.
# 7. Then to Financial District for Sandra.
#
# We compute each leg sequentially taking into account travel times and waiting for the meeting windows.

itinerary = []

# Start time at Union Square, 9:00am (540 minutes)
current_time = 540
current_location = "Union Square"

# Leg 1: Travel to Marina District for Joshua
travel = travel_times[(current_location, "Marina District")]
current_time = add_minutes(current_time, travel)
current_location = "Marina District"
# Wait until Joshua's window opens:
start_meeting = max(current_time, meeting_info["Joshua"]["window_start"])
end_meeting = start_meeting + meeting_info["Joshua"]["duration"]
itinerary.append({
    "action": "meet",
    "location": meeting_info["Joshua"]["location"],
    "person": "Joshua",
    "start_time": minutes_to_time_str(start_meeting),
    "end_time": minutes_to_time_str(end_meeting)
})
current_time = end_meeting  # finish meeting here

# Leg 2: Travel from Marina District to Nob Hill for Kenneth
travel = travel_times[(current_location, "Nob Hill")]
current_time = add_minutes(current_time, travel)
current_location = "Nob Hill"
start_meeting = max(current_time, meeting_info["Kenneth"]["window_start"])
end_meeting = start_meeting + meeting_info["Kenneth"]["duration"]
itinerary.append({
    "action": "meet",
    "location": meeting_info["Kenneth"]["location"],
    "person": "Kenneth",
    "start_time": minutes_to_time_str(start_meeting),
    "end_time": minutes_to_time_str(end_meeting)
})
current_time = end_meeting

# Leg 3: Travel from Nob Hill to Sunset District for Betty
travel = travel_times[(current_location, "Sunset District")]
current_time = add_minutes(current_time, travel)
current_location = "Sunset District"
start_meeting = max(current_time, meeting_info["Betty"]["window_start"])
end_meeting = start_meeting + meeting_info["Betty"]["duration"]
itinerary.append({
    "action": "meet",
    "location": meeting_info["Betty"]["location"],
    "person": "Betty",
    "start_time": minutes_to_time_str(start_meeting),
    "end_time": minutes_to_time_str(end_meeting)
})
current_time = end_meeting

# Leg 4: Travel from Sunset District to Presidio for Kimberly
travel = travel_times[(current_location, "Presidio")]
current_time = add_minutes(current_time, travel)
current_location = "Presidio"
start_meeting = max(current_time, meeting_info["Kimberly"]["window_start"])
end_meeting = start_meeting + meeting_info["Kimberly"]["duration"]
itinerary.append({
    "action": "meet",
    "location": meeting_info["Kimberly"]["location"],
    "person": "Kimberly",
    "start_time": minutes_to_time_str(start_meeting),
    "end_time": minutes_to_time_str(end_meeting)
})
current_time = end_meeting

# Evening block:
# Leg 5: From Presidio to Chinatown for Deborah
travel = travel_times[(current_location, "Chinatown")]
current_time = add_minutes(current_time, travel)
current_location = "Chinatown"
start_meeting = max(current_time, meeting_info["Deborah"]["window_start"])
end_meeting = start_meeting + meeting_info["Deborah"]["duration"]
itinerary.append({
    "action": "meet",
    "location": meeting_info["Deborah"]["location"],
    "person": "Deborah",
    "start_time": minutes_to_time_str(start_meeting),
    "end_time": minutes_to_time_str(end_meeting)
})
current_time = end_meeting

# Leg 6: From Chinatown to North Beach for Steven
travel = travel_times[(current_location, "North Beach")]
current_time = add_minutes(current_time, travel)
current_location = "North Beach"
start_meeting = max(current_time, meeting_info["Steven"]["window_start"])
end_meeting = start_meeting + meeting_info["Steven"]["duration"]
itinerary.append({
    "action": "meet",
    "location": meeting_info["Steven"]["location"],
    "person": "Steven",
    "start_time": minutes_to_time_str(start_meeting),
    "end_time": minutes_to_time_str(end_meeting)
})
current_time = end_meeting

# Leg 7: From North Beach to Financial District for Sandra
travel = travel_times[(current_location, "Financial District")]
current_time = add_minutes(current_time, travel)
current_location = "Financial District"
start_meeting = max(current_time, meeting_info["Sandra"]["window_start"])
end_meeting = start_meeting + meeting_info["Sandra"]["duration"]
itinerary.append({
    "action": "meet",
    "location": meeting_info["Sandra"]["location"],
    "person": "Sandra",
    "start_time": minutes_to_time_str(start_meeting),
    "end_time": minutes_to_time_str(end_meeting)
})
current_time = end_meeting

# Build final itinerary dictionary
result = {"itinerary": itinerary}

# Output the resulting schedule as JSON
print(json.dumps(result, indent=2))