#!/usr/bin/env python3
import json

# Convert time in minutes (since midnight) to "H:MM" format (24-hour, no leading zero for hour)
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times (in minutes) between locations.
# The keys are starting locations, and the values are dictionaries mapping destination locations to travel times.
travel = {
    "Richmond District": {
        "The Castro": 16,
        "Nob Hill": 17,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Chinatown": 20,
        "Russian Hill": 13,
        "Alamo Square": 13,
        "Bayview": 27
    },
    "The Castro": {
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Chinatown": 22,
        "Russian Hill": 18,
        "Alamo Square": 8,
        "Bayview": 19
    },
    "Nob Hill": {
        "Richmond District": 14,
        "The Castro": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Mission District": 13,
        "Chinatown": 6,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "Bayview": 19
    },
    "Marina District": {
        "Richmond District": 11,
        "The Castro": 22,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Chinatown": 15,
        "Russian Hill": 8,
        "Alamo Square": 15,
        "Bayview": 27
    },
    "Pacific Heights": {
        "Richmond District": 12,
        "The Castro": 16,
        "Nob Hill": 8,
        "Marina District": 6,
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Chinatown": 11,
        "Russian Hill": 7,
        "Alamo Square": 10,
        "Bayview": 22
    },
    "Haight-Ashbury": {
        "Richmond District": 10,
        "The Castro": 6,
        "Nob Hill": 15,
        "Marina District": 17,
        "Pacific Heights": 12,
        "Mission District": 11,
        "Chinatown": 19,
        "Russian Hill": 17,
        "Alamo Square": 5,
        "Bayview": 18
    },
    "Mission District": {
        "Richmond District": 20,
        "The Castro": 7,
        "Nob Hill": 12,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Haight-Ashbury": 12,
        "Chinatown": 16,
        "Russian Hill": 15,
        "Alamo Square": 11,
        "Bayview": 14
    },
    "Chinatown": {
        "Richmond District": 20,
        "The Castro": 22,
        "Nob Hill": 9,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Haight-Ashbury": 19,
        "Mission District": 17,
        "Russian Hill": 7,
        "Alamo Square": 17,
        "Bayview": 20
    },
    "Russian Hill": {
        "Richmond District": 14,
        "The Castro": 21,
        "Nob Hill": 5,
        "Marina District": 7,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Chinatown": 9,
        "Alamo Square": 15,
        "Bayview": 23
    },
    "Alamo Square": {
        "Richmond District": 11,
        "The Castro": 8,
        "Nob Hill": 11,
        "Marina District": 15,
        "Pacific Heights": 10,
        "Haight-Ashbury": 5,
        "Mission District": 10,
        "Chinatown": 15,
        "Russian Hill": 13,
        "Bayview": 16
    },
    "Bayview": {
        "Richmond District": 25,
        "The Castro": 19,
        "Nob Hill": 20,
        "Marina District": 27,
        "Pacific Heights": 23,
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Chinatown": 19,
        "Russian Hill": 23,
        "Alamo Square": 16
    }
}

# Friends meeting constraints.
# Times are represented in minutes after midnight.
# For example, 9:00 AM is 9*60 = 540 minutes.
friends = {
    "Matthew": {
        "location": "The Castro",
        "avail_start": 16 * 60 + 30,  # 16:30 -> 990
        "avail_end": 20 * 60,         # 20:00 -> 1200
        "duration": 45
    },
    "Rebecca": {
        "location": "Nob Hill",
        "avail_start": 15 * 60 + 15,  # 15:15 -> 915
        "avail_end": 19 * 60 + 15,    # 19:15 -> 1155
        "duration": 105
    },
    "Brian": {
        "location": "Marina District",
        "avail_start": 14 * 60 + 15,  # 14:15 -> 855
        "avail_end": 22 * 60,         # 22:00 -> 1320
        "duration": 30
    },
    "Emily": {
        "location": "Pacific Heights",
        "avail_start": 11 * 60 + 15,  # 11:15 -> 675
        "avail_end": 19 * 60 + 45,    # 19:45 -> 1185
        "duration": 15
    },
    "Karen": {
        "location": "Haight-Ashbury",
        "avail_start": 11 * 60 + 45,  # 11:45 -> 705
        "avail_end": 17 * 60 + 30,    # 17:30 -> 1050
        "duration": 30
    },
    "Stephanie": {
        "location": "Mission District",
        "avail_start": 13 * 60,       # 13:00 -> 780
        "avail_end": 15 * 60 + 45,    # 15:45 -> 945
        "duration": 75
    },
    "James": {
        "location": "Chinatown",
        "avail_start": 14 * 60 + 30,  # 14:30 -> 870
        "avail_end": 19 * 60,         # 19:00 -> 1140
        "duration": 120
    },
    "Steven": {
        "location": "Russian Hill",
        "avail_start": 14 * 60,       # 14:00 -> 840
        "avail_end": 20 * 60,         # 20:00 -> 1200
        "duration": 30
    },
    "Elizabeth": {
        "location": "Alamo Square",
        "avail_start": 13 * 60,       # 13:00 -> 780
        "avail_end": 17 * 60 + 15,    # 17:15 -> 1035
        "duration": 120
    },
    "William": {
        "location": "Bayview",
        "avail_start": 18 * 60 + 15,  # 18:15 -> 1095
        "avail_end": 20 * 60 + 15,    # 20:15 -> 1215
        "duration": 90
    }
}

# Global variables to track the best schedule found (maximizing number of meetings)
best_schedule = []
best_count = 0

def backtrack(current_location, current_time, remaining_friends, current_schedule):
    global best_schedule, best_count
    # Update best schedule if current schedule has more meetings
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = current_schedule.copy()
    # Try scheduling each of the remaining friends
    for friend in remaining_friends:
        friend_info = friends[friend]
        dest = friend_info["location"]
        # Get travel time from current location to destination
        # If destination not found in travel[current_location] then skip (should not happen)
        if dest not in travel[current_location]:
            continue
        travel_time = travel[current_location][dest]
        arrival_time = current_time + travel_time
        # Meeting can only start no earlier than the friend's available start
        meeting_start = max(arrival_time, friend_info["avail_start"])
        meeting_end = meeting_start + friend_info["duration"]
        # Check if the meeting fits in the friend's available window
        if meeting_end <= friend_info["avail_end"]:
            # Create a meeting entry (store times in minutes for now)
            meeting = {
                "action": "meet",
                "location": dest,
                "person": friend,
                "start_time": meeting_start,
                "end_time": meeting_end
            }
            new_schedule = current_schedule + [meeting]
            new_remaining = remaining_friends.copy()
            new_remaining.remove(friend)
            backtrack(dest, meeting_end, new_remaining, new_schedule)

def main():
    # Start at Richmond District at 9:00 AM (9*60 = 540 minutes)
    start_location = "Richmond District"
    start_time = 9 * 60  # 540 minutes
    all_friends = list(friends.keys())
    backtrack(start_location, start_time, all_friends, [])
    
    # Format the best schedule's times using format_time function.
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": meeting["action"],
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": format_time(meeting["start_time"]),
            "end_time": format_time(meeting["end_time"])
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()