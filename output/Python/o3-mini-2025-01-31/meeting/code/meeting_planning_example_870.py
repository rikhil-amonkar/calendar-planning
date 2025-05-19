#!/usr/bin/env python3
import json

# Utility functions for time conversion
def minutes_to_time(m):
    h = m // 60
    m_remainder = m % 60
    return f"{h}:{m_remainder:02d}"

# Travel times between locations (in minutes)
travel_times = {
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,

    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,

    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,

    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Russian Hill"): 13,

    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Russian Hill"): 13,

    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,

    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,

    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Russian Hill"): 15,

    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Russian Hill"): 5,

    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Nob Hill"): 5,
}

# Meeting constraints as input variables:
# Times are represented in minutes from midnight.
meetings = {
    "Linda": {
        "location": "Marina District",
        "avail_start": 18*60,      # 18:00 -> 1080
        "avail_end": 22*60,        # 22:00 -> 1320
        "duration": 30
    },
    "Kenneth": {
        "location": "The Castro",
        "avail_start": 14*60 + 45, # 14:45 -> 885
        "avail_end": 16*60 + 15,   # 16:15 -> 975
        "duration": 30
    },
    "Kimberly": {
        "location": "Richmond District",
        "avail_start": 14*60 + 15, # 14:15 -> 855
        "avail_end": 22*60,        # 22:00 -> 1320
        "duration": 30
    },
    "Paul": {
        "location": "Alamo Square",
        "avail_start": 21*60,      # 21:00 -> 1260
        "avail_end": 21*60 + 30,   # 21:30 -> 1290
        "duration": 15
    },
    "Carol": {
        "location": "Financial District",
        "avail_start": 10*60 + 15, # 10:15 -> 615
        "avail_end": 12*60,        # 12:00 -> 720
        "duration": 60
    },
    "Brian": {
        "location": "Presidio",
        "avail_start": 10*60,      # 10:00 -> 600
        "avail_end": 21*60 + 30,   # 21:30 -> 1290
        "duration": 75
    },
    "Laura": {
        "location": "Mission District",
        "avail_start": 16*60 + 15, # 16:15 -> 975
        "avail_end": 20*60 + 30,   # 20:30 -> 1230
        "duration": 30
    },
    "Sandra": {
        "location": "Nob Hill",
        "avail_start": 9*60 + 15,  # 9:15 -> 555
        "avail_end": 18*60 + 30,   # 18:30 -> 1110
        "duration": 60
    },
    "Karen": {
        "location": "Russian Hill",
        "avail_start": 18*60 + 30, # 18:30 -> 1110
        "avail_end": 22*60,        # 22:00 -> 1320
        "duration": 75
    }
}

# Global variable to store the best schedule (max number of meetings scheduled)
best_schedule = []
best_count = 0

def can_schedule(current_loc, current_time, meeting):
    # Get travel time from current_loc to meeting location
    key = (current_loc, meeting["location"])
    if key not in travel_times:
        return None  # no travel possible
    travel = travel_times[key]
    arrival_time = current_time + travel
    # The meeting should start no earlier than meeting's available start time.
    meeting_start = max(arrival_time, meeting["avail_start"])
    meeting_end = meeting_start + meeting["duration"]
    if meeting_end <= meeting["avail_end"]:
        return meeting_start, meeting_end, travel
    else:
        return None

def backtrack(current_loc, current_time, remaining, schedule):
    global best_schedule, best_count

    # If no remaining meetings, update best schedule if needed.
    if len(schedule) > best_count:
        best_schedule = schedule.copy()
        best_count = len(schedule)
    # Try to schedule each remaining meeting.
    for person in list(remaining.keys()):
        meeting = remaining[person]
        possibility = can_schedule(current_loc, current_time, meeting)
        if possibility:
            meeting_start, meeting_end, travel_used = possibility
            # Create a meeting record
            meeting_record = {
                "action": "meet",
                "location": meeting["location"],
                "person": person,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            # Prepare new remaining dictionary without the scheduled meeting.
            new_remaining = remaining.copy()
            del new_remaining[person]
            # Continue backtracking from new location and time.
            backtrack(meeting["location"], meeting_end, new_remaining, schedule + [meeting_record])
    # Also update best if current schedule is longer.
    if len(schedule) > best_count:
        best_schedule = schedule.copy()
        best_count = len(schedule)

def main():
    # Starting point: Pacific Heights at 9:00AM (9*60 = 540 minutes)
    start_loc = "Pacific Heights"
    start_time = 9*60  # 9:00 AM in minutes
    # Create a copy of meetings for remaining meetings.
    remaining_meetings = meetings.copy()
    # Run backtracking search to schedule meetings.
    backtrack(start_loc, start_time, remaining_meetings, [])
    # Output the best itinerary in the required JSON structure.
    output = {"itinerary": best_schedule}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()