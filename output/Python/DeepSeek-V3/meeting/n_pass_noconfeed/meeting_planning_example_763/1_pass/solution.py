import json
from itertools import permutations

# Travel times dictionary: travel_times[from][to] = minutes
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

# Friend data: name, location, available start, available end, min_duration (minutes)
friends = [
    ("Richard", "Embarcadero", (15, 15), (18, 45), 90),
    ("Mark", "Pacific Heights", (15, 0), (17, 0), 45),
    ("Matthew", "Russian Hill", (17, 30), (21, 0), 90),
    ("Rebecca", "Haight-Ashbury", (14, 45), (18, 0), 60),
    ("Melissa", "Golden Gate Park", (13, 45), (17, 30), 90),
    ("Margaret", "Fisherman's Wharf", (14, 45), (20, 15), 15),
    ("Emily", "Sunset District", (15, 45), (17, 0), 45),
    ("George", "The Castro", (14, 0), (16, 15), 75)
]

def time_to_minutes(time_tuple):
    return time_tuple[0] * 60 + time_tuple[1]

def minutes_to_time(minutes):
    return (minutes // 60, minutes % 60)

def format_time(time_tuple):
    return f"{time_tuple[0]}:{time_tuple[1]:02d}"

def calculate_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Try all possible orders of meeting friends (limited to 4 for performance)
    for friend_order in permutations(friends, min(4, len(friends))):
        current_location = "Chinatown"
        current_time = time_to_minutes((9, 0))
        schedule = []
        meetings = 0
        
        for friend in friend_order:
            name, location, avail_start, avail_end, min_duration = friend
            avail_start_min = time_to_minutes(avail_start)
            avail_end_min = time_to_minutes(avail_end)
            
            # Calculate travel time
            travel_time = travel_times[current_location].get(location, float('inf'))
            arrival_time = current_time + travel_time
            
            # Check if we can meet this friend
            if arrival_time > avail_end_min:
                continue  # Can't meet, arrived too late
            
            # Calculate possible meeting window
            meeting_start = max(arrival_time, avail_start_min)
            meeting_end = min(meeting_start + min_duration, avail_end_min)
            
            if meeting_end - meeting_start < min_duration:
                continue  # Can't meet for required duration
            
            # Add to schedule
            schedule.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": format_time(minutes_to_time(meeting_start)),
                "end_time": format_time(minutes_to_time(meeting_end))
            })
            meetings += 1
            current_location = location
            current_time = meeting_end
        
        if meetings > max_meetings or (meetings == max_meetings and len(schedule) > len(best_schedule)):
            max_meetings = meetings
            best_schedule = schedule
    
    return best_schedule

def main():
    schedule = calculate_schedule()
    result = {"itinerary": schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()