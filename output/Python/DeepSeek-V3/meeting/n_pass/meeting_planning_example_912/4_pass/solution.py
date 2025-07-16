import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Union Square": {
        "Presidio": 24, "Alamo Square": 15, "Marina District": 18, "Financial District": 9,
        "Nob Hill": 9, "Sunset District": 27, "Chinatown": 7, "Russian Hill": 13, "North Beach": 10,
        "Haight-Ashbury": 18
    },
    "Presidio": {
        "Union Square": 22, "Alamo Square": 19, "Marina District": 11, "Financial District": 23,
        "Nob Hill": 18, "Sunset District": 15, "Chinatown": 21, "Russian Hill": 14, "North Beach": 18,
        "Haight-Ashbury": 15
    },
    "Alamo Square": {
        "Union Square": 14, "Presidio": 17, "Marina District": 15, "Financial District": 17,
        "Nob Hill": 11, "Sunset District": 16, "Chinatown": 15, "Russian Hill": 13, "North Beach": 15,
        "Haight-Ashbury": 5
    },
    "Marina District": {
        "Union Square": 16, "Presidio": 10, "Alamo Square": 15, "Financial District": 17,
        "Nob Hill": 12, "Sunset District": 19, "Chinatown": 15, "Russian Hill": 8, "North Beach": 11,
        "Haight-Ashbury": 16
    },
    "Financial District": {
        "Union Square": 9, "Presidio": 22, "Alamo Square": 17, "Marina District": 15,
        "Nob Hill": 8, "Sunset District": 30, "Chinatown": 5, "Russian Hill": 11, "North Beach": 7,
        "Haight-Ashbury": 19
    },
    "Nob Hill": {
        "Union Square": 7, "Presidio": 17, "Alamo Square": 11, "Marina District": 11,
        "Financial District": 9, "Sunset District": 24, "Chinatown": 6, "Russian Hill": 5, "North Beach": 8,
        "Haight-Ashbury": 13
    },
    "Sunset District": {
        "Union Square": 30, "Presidio": 16, "Alamo Square": 17, "Marina District": 21,
        "Financial District": 30, "Nob Hill": 27, "Chinatown": 30, "Russian Hill": 24, "North Beach": 28,
        "Haight-Ashbury": 15
    },
    "Chinatown": {
        "Union Square": 7, "Presidio": 19, "Alamo Square": 17, "Marina District": 12,
        "Financial District": 5, "Nob Hill": 9, "Sunset District": 29, "Russian Hill": 7, "North Beach": 3,
        "Haight-Ashbury": 19
    },
    "Russian Hill": {
        "Union Square": 10, "Presidio": 14, "Alamo Square": 15, "Marina District": 7,
        "Financial District": 11, "Nob Hill": 5, "Sunset District": 23, "Chinatown": 9, "North Beach": 5,
        "Haight-Ashbury": 17
    },
    "North Beach": {
        "Union Square": 7, "Presidio": 17, "Alamo Square": 16, "Marina District": 9,
        "Financial District": 8, "Nob Hill": 7, "Sunset District": 27, "Chinatown": 6, "Russian Hill": 4,
        "Haight-Ashbury": 18
    },
    "Haight-Ashbury": {
        "Union Square": 19, "Presidio": 15, "Alamo Square": 5, "Marina District": 17,
        "Financial District": 21, "Nob Hill": 15, "Sunset District": 15, "Chinatown": 19, "Russian Hill": 17,
        "North Beach": 19
    }
}

# Friend constraints
friends = [
    {"name": "Kimberly", "location": "Presidio", "start": "15:30", "end": "16:00", "duration": 15},
    {"name": "Elizabeth", "location": "Alamo Square", "start": "19:15", "end": "20:15", "duration": 15},
    {"name": "Joshua", "location": "Marina District", "start": "10:30", "end": "14:15", "duration": 45},
    {"name": "Sandra", "location": "Financial District", "start": "19:30", "end": "20:15", "duration": 45},
    {"name": "Kenneth", "location": "Nob Hill", "start": "12:45", "end": "21:45", "duration": 30},
    {"name": "Betty", "location": "Sunset District", "start": "14:00", "end": "19:00", "duration": 60},
    {"name": "Deborah", "location": "Chinatown", "start": "17:15", "end": "20:30", "duration": 15},
    {"name": "Barbara", "location": "Russian Hill", "start": "17:30", "end": "21:15", "duration": 120},
    {"name": "Steven", "location": "North Beach", "start": "17:45", "end": "20:45", "duration": 90},
    {"name": "Daniel", "location": "Haight-Ashbury", "start": "18:30", "end": "18:45", "duration": 15}
]

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc]

def schedule_meeting(current_time, current_location, friend):
    start_avail = time_to_minutes(friend["start"])
    end_avail = time_to_minutes(friend["end"])
    duration = friend["duration"]
    
    travel_time = get_travel_time(current_location, friend["location"])
    earliest_start = current_time + travel_time
    latest_start = end_avail - duration
    
    if earliest_start > latest_start:
        return None
        
    start_meeting = max(earliest_start, start_avail)
    end_meeting = start_meeting + duration
    
    if end_meeting > end_avail:
        return None
        
    return {
        "action": "meet",
        "location": friend["location"],
        "person": friend["name"],
        "start_time": minutes_to_time(start_meeting),
        "end_time": minutes_to_time(end_meeting)
    }

def find_best_schedule():
    # Sort friends by earliest possible meeting time (start time + travel time from Union Square)
    sorted_friends = sorted(friends, key=lambda f: (
        time_to_minutes(f["start"]) + get_travel_time("Union Square", f["location"])
    ))
    
    best_schedule = []
    best_count = 0
    
    # Try different starting orders to maximize meetings
    for i in range(min(3, len(friends))):  # Try first 3 as starting points
        current_schedule = []
        current_time = time_to_minutes("9:00")
        current_location = "Union Square"
        visited = set()
        
        # Start with the ith friend
        first_meeting = schedule_meeting(current_time, current_location, sorted_friends[i])
        if first_meeting:
            current_schedule.append(first_meeting)
            visited.add(sorted_friends[i]["name"])
            current_time = time_to_minutes(first_meeting["end_time"])
            current_location = first_meeting["location"]
            
            # Try to schedule remaining friends
            remaining_friends = [f for f in sorted_friends if f["name"] not in visited]
            for friend in remaining_friends:
                meeting = schedule_meeting(current_time, current_location, friend)
                if meeting:
                    current_schedule.append(meeting)
                    visited.add(friend["name"])
                    current_time = time_to_minutes(meeting["end_time"])
                    current_location = meeting["location"]
            
            if len(current_schedule) > best_count:
                best_schedule = current_schedule
                best_count = len(best_schedule)
                if best_count == len(friends):
                    break
    
    return best_schedule

def main():
    best_schedule = find_best_schedule()
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()