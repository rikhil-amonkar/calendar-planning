#!/usr/bin/env python3
import json
import copy

# Convert time in minutes to string "H:MM" (24-hour, no leading zero for hour)
def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times (in minutes) between locations as provided
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
        "The Castro": 22,
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

# Define friend meeting constraints.
# Times are expressed in minutes after midnight.
# 9:00AM is 540.
# Friends:
# Amanda: Marina District, available 14:45 (885) to 19:30 (1170), min meeting 105
# Melissa: The Castro, available 9:30 (570) to 17:00 (1020), min meeting 30
# Jeffrey: Fisherman's Wharf, available 12:45 (765) to 18:45 (1125), min meeting 120
# Matthew: Bayview, available 10:15 (615) to 13:15 (795), min meeting 30
# Nancy: Pacific Heights, available 17:00 (1020) to 21:30 (1290), min meeting 105
# Karen: Mission District, available 17:30 (1050) to 20:30 (1230), min meeting 105
# Robert: Alamo Square, available 11:15 (675) to 17:30 (1050), min meeting 120
# Joseph: Golden Gate Park, available 8:30 (510) to 21:15 (1275), min meeting 105
friends = [
    {
        "name": "Amanda",
        "location": "Marina District",
        "avail_start": 14 * 60 + 45,  # 14:45 -> 885
        "avail_end": 19 * 60 + 30,      # 19:30 -> 1170
        "duration": 105
    },
    {
        "name": "Melissa",
        "location": "The Castro",
        "avail_start": 9 * 60 + 30,   # 9:30 -> 570
        "avail_end": 17 * 60,         # 17:00 -> 1020
        "duration": 30
    },
    {
        "name": "Jeffrey",
        "location": "Fisherman's Wharf",
        "avail_start": 12 * 60 + 45,  # 12:45 -> 765
        "avail_end": 18 * 60 + 45,    # 18:45 -> 1125
        "duration": 120
    },
    {
        "name": "Matthew",
        "location": "Bayview",
        "avail_start": 10 * 60 + 15,  # 10:15 -> 615
        "avail_end": 13 * 60 + 15,    # 13:15 -> 795
        "duration": 30
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "avail_start": 17 * 60,       # 17:00 -> 1020
        "avail_end": 21 * 60 + 30,      # 21:30 -> 1290
        "duration": 105
    },
    {
        "name": "Karen",
        "location": "Mission District",
        "avail_start": 17 * 60 + 30,  # 17:30 -> 1050
        "avail_end": 20 * 60 + 30,    # 20:30 -> 1230
        "duration": 105
    },
    {
        "name": "Robert",
        "location": "Alamo Square",
        "avail_start": 11 * 60 + 15,  # 11:15 -> 675
        "avail_end": 17 * 60 + 30,    # 17:30 -> 1050
        "duration": 120
    },
    {
        "name": "Joseph",
        "location": "Golden Gate Park",
        "avail_start": 8 * 60 + 30,   # 8:30 -> 510
        "avail_end": 21 * 60 + 15,    # 21:15 -> 1275
        "duration": 105
    }
]

# Global variables to store the best (optimal) schedule found.
best_schedule = []
best_count = 0

def search(current_time, current_location, remaining_friends, current_schedule):
    global best_schedule, best_count
    found_next = False
    for i, friend in enumerate(remaining_friends):
        # Get travel time from current location to friend's meeting location.
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when both you arrive and the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting can finish before the friend leaves.
        if meeting_end <= friend["avail_end"]:
            found_next = True
            # Create a new meeting record.
            meeting_record = {
                "person": friend["name"],
                "location": friend["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            # Create new schedule with this meeting appended.
            new_schedule = current_schedule + [meeting_record]
            # Exclude the current friend from remaining list.
            new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            # Continue searching from the end of this meeting.
            search(meeting_end, friend["location"], new_remaining, new_schedule)
    # If no further meeting can be added, update global best if current schedule is better.
    if not found_next:
        if len(current_schedule) > best_count:
            best_count = len(current_schedule)
            best_schedule = current_schedule

def main():
    # Start time: 9:00 AM (540 minutes after midnight) at Presidio.
    start_time = 9 * 60  # 540
    start_location = "Presidio"
    # Begin search for the optimal meeting schedule.
    search(start_time, start_location, friends, [])
    
    # Build itinerary list in required JSON format.
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": format_time(meeting["start"]),
            "end_time": format_time(meeting["end"])
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
    
if __name__ == '__main__':
    main()