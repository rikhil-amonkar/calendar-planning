import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Chinatown": {
        "Embarcadero": 5,
        "Pacific Heights": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 8,
        "Sunset District": 29,
        "The Castro": 22
    },
    "Embarcadero": {
        "Chinatown": 7,
        "Pacific Heights": 11,
        "Russian Hill": 8,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Sunset District": 30,
        "The Castro": 25
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Embarcadero": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Sunset District": 21,
        "The Castro": 16
    },
    "Russian Hill": {
        "Chinatown": 9,
        "Embarcadero": 8,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Golden Gate Park": 21,
        "Fisherman's Wharf": 7,
        "Sunset District": 23,
        "The Castro": 21
    },
    "Haight-Ashbury": {
        "Chinatown": 19,
        "Embarcadero": 20,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "Sunset District": 15,
        "The Castro": 6
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Embarcadero": 25,
        "Pacific Heights": 16,
        "Russian Hill": 19,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Sunset District": 10,
        "The Castro": 13
    },
    "Fisherman's Wharf": {
        "Chinatown": 12,
        "Embarcadero": 8,
        "Pacific Heights": 12,
        "Russian Hill": 7,
        "Haight-Ashbury": 22,
        "Golden Gate Park": 25,
        "Sunset District": 27,
        "The Castro": 27
    },
    "Sunset District": {
        "Chinatown": 30,
        "Embarcadero": 30,
        "Pacific Heights": 21,
        "Russian Hill": 24,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "The Castro": 17
    },
    "The Castro": {
        "Chinatown": 22,
        "Embarcadero": 22,
        "Pacific Heights": 16,
        "Russian Hill": 18,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 24,
        "Sunset District": 17
    }
}

# Friend data: name -> (location, start_time, end_time, min_duration)
friends = {
    "Richard": ("Embarcadero", (15, 15), (18, 45), 90),
    "Mark": ("Pacific Heights", (15, 0), (17, 0), 45),
    "Matthew": ("Russian Hill", (17, 30), (21, 0), 90),
    "Rebecca": ("Haight-Ashbury", (14, 45), (18, 0), 60),
    "Melissa": ("Golden Gate Park", (13, 45), (17, 30), 90),
    "Margaret": ("Fisherman's Wharf", (14, 45), (20, 15), 15),
    "Emily": ("Sunset District", (15, 45), (17, 0), 45),
    "George": ("The Castro", (14, 0), (16, 15), 75)
}

def time_to_minutes(time_tuple):
    return time_tuple[0] * 60 + time_tuple[1]

def minutes_to_time(minutes):
    return (minutes // 60, minutes % 60)

def format_time(time_tuple):
    return f"{time_tuple[0]}:{time_tuple[1]:02d}"

def can_meet(friend, start_time_min, end_time_min):
    _, (avail_start_h, avail_start_m), (avail_end_h, avail_end_m), min_duration = friend
    avail_start = avail_start_h * 60 + avail_start_m
    avail_end = avail_end_h * 60 + avail_end_m
    
    # Calculate possible meeting window
    meeting_start = max(start_time_min, avail_start)
    meeting_end = min(end_time_min, avail_end)
    
    if meeting_end - meeting_start >= min_duration:
        return (meeting_start, meeting_start + min_duration)
    return None

def calculate_schedule(permutation):
    current_location = "Chinatown"
    current_time = 9 * 60  # 9:00 AM in minutes
    schedule = []
    
    for friend_name in permutation:
        friend_data = friends[friend_name]
        location = friend_data[0]
        
        # Calculate travel time
        travel_time = travel_times[current_location].get(location, float('inf'))
        arrival_time = current_time + travel_time
        
        # Try to meet
        meeting_window = can_meet(friend_data, arrival_time, friend_data[2][0] * 60 + friend_data[2][1])
        if meeting_window:
            start_time = meeting_window[0]
            end_time = meeting_window[1]
            schedule.append({
                "action": "meet",
                "location": location,
                "person": friend_name,
                "start_time": format_time(minutes_to_time(start_time)),
                "end_time": format_time(minutes_to_time(end_time))
            })
            current_time = end_time
            current_location = location
        else:
            return None  # This permutation doesn't work
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    return len(schedule)

def main():
    best_schedule = []
    best_score = 0
    
    # Try all permutations of friends (but limit to reasonable length due to computational constraints)
    for perm in permutations(friends.keys(), min(5, len(friends))):
        schedule = calculate_schedule(perm)
        score = evaluate_schedule(schedule)
        if score > best_score:
            best_score = score
            best_schedule = schedule
    
    # Output the best schedule found
    output = {
        "itinerary": best_schedule
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()