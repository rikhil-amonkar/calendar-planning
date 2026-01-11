import json
from itertools import permutations

# Travel times matrix
travel_times = {
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Chinatown": 23,
        "Alamo Square": 10,
        "North Beach": 24,
        "Russian Hill": 19
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "The Castro": 6,
        "Chinatown": 19,
        "Alamo Square": 5,
        "North Beach": 19,
        "Russian Hill": 17
    },
    "Fisherman's Wharf": {
        "Golden Gate Park": 25,
        "Haight-Ashbury": 22,
        "The Castro": 26,
        "Chinatown": 12,
        "Alamo Square": 20,
        "North Beach": 6,
        "Russian Hill": 7
    },
    "The Castro": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 6,
        "Fisherman's Wharf": 24,
        "Chinatown": 20,
        "Alamo Square": 8,
        "North Beach": 20,
        "Russian Hill": 18
    },
    "Chinatown": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 8,
        "The Castro": 22,
        "Alamo Square": 17,
        "North Beach": 3,
        "Russian Hill": 7
    },
    "Alamo Square": {
        "Golden Gate Park": 9,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Chinatown": 16,
        "North Beach": 15,
        "Russian Hill": 13
    },
    "North Beach": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Chinatown": 6,
        "Alamo Square": 16,
        "Russian Hill": 4
    },
    "Russian Hill": {
        "Golden Gate Park": 21,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Chinatown": 9,
        "Alamo Square": 15,
        "North Beach": 5
    }
}

# Friend data: location, window start/end in minutes from midnight, min duration
friends = [
    {"name": "Carol", "location": "Haight-Ashbury", "start": 21*60+30, "end": 22*60+30, "min_dur": 60},
    {"name": "Laura", "location": "Fisherman's Wharf", "start": 11*60+45, "end": 21*60+30, "min_dur": 60},
    {"name": "Karen", "location": "The Castro", "start": 7*60+15, "end": 14*60, "min_dur": 75},
    {"name": "Elizabeth", "location": "Chinatown", "start": 12*60+15, "end": 21*60+30, "min_dur": 75},
    {"name": "Deborah", "location": "Alamo Square", "start": 12*60, "end": 15*60, "min_dur": 105},
    {"name": "Jason", "location": "North Beach", "start": 14*60+45, "end": 19*60, "min_dur": 90},
    {"name": "Steven", "location": "Russian Hill", "start": 14*60+45, "end": 18*60+30, "min_dur": 120}
]

def time_str(minutes):
    """Convert minutes since midnight to 'H:MM' format"""
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def schedule_permutation(perm):
    """Try to schedule a given permutation of friends, return (meetings, total_meeting_time)"""
    current_location = "Golden Gate Park"
    current_time = 9 * 60  # 9:00 AM
    meetings = []
    total_meeting_time = 0
    
    for friend in perm:
        # Travel to friend's location
        travel = travel_times[current_location][friend["location"]]
        current_time += travel
        
        # Arrival time
        arrival = current_time
        
        # Start meeting at earliest possible time
        start_meeting = max(arrival, friend["start"])
        if start_meeting > friend["end"]:
            return None, 0  # Cannot meet, window already passed
        
        # End meeting
        end_meeting = min(start_meeting + friend["min_dur"], friend["end"])
        if end_meeting - start_meeting < friend["min_dur"]:
            return None, 0  # Cannot meet for minimum duration
        
        # Add meeting
        meetings.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": time_str(start_meeting),
            "end_time": time_str(end_meeting)
        })
        total_meeting_time += end_meeting - start_meeting
        current_time = end_meeting
        current_location = friend["location"]
    
    return meetings, total_meeting_time

def main():
    best_meetings = []
    best_count = 0
    best_total_time = 0
    
    # Try all permutations of friends (7! = 5040, manageable)
    for perm in permutations(friends):
        meetings, total_time = schedule_permutation(perm)
        if meetings is None:
            continue
        
        if len(meetings) > best_count or (len(meetings) == best_count and total_time > best_total_time):
            best_count = len(meetings)
            best_total_time = total_time
            best_meetings = meetings
    
    # Output result
    result = {"itinerary": best_meetings}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()