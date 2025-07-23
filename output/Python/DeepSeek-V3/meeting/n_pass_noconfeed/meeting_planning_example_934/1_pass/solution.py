import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary: travel_times[from][to] = minutes
travel_times = {
    "Nob Hill": {
        "Embarcadero": 9, "The Castro": 17, "Haight-Ashbury": 13, "Union Square": 7,
        "North Beach": 8, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 17,
        "Marina District": 11, "Russian Hill": 5
    },
    "Embarcadero": {
        "Nob Hill": 10, "The Castro": 25, "Haight-Ashbury": 21, "Union Square": 10,
        "North Beach": 5, "Pacific Heights": 11, "Chinatown": 7, "Golden Gate Park": 25,
        "Marina District": 12, "Russian Hill": 8
    },
    "The Castro": {
        "Nob Hill": 16, "Embarcadero": 22, "Haight-Ashbury": 6, "Union Square": 19,
        "North Beach": 20, "Pacific Heights": 16, "Chinatown": 22, "Golden Gate Park": 11,
        "Marina District": 21, "Russian Hill": 18
    },
    "Haight-Ashbury": {
        "Nob Hill": 15, "Embarcadero": 20, "The Castro": 6, "Union Square": 19,
        "North Beach": 19, "Pacific Heights": 12, "Chinatown": 19, "Golden Gate Park": 7,
        "Marina District": 17, "Russian Hill": 17
    },
    "Union Square": {
        "Nob Hill": 9, "Embarcadero": 11, "The Castro": 17, "Haight-Ashbury": 18,
        "North Beach": 10, "Pacific Heights": 15, "Chinatown": 7, "Golden Gate Park": 22,
        "Marina District": 18, "Russian Hill": 13
    },
    "North Beach": {
        "Nob Hill": 7, "Embarcadero": 6, "The Castro": 23, "Haight-Ashbury": 18,
        "Union Square": 7, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 22,
        "Marina District": 9, "Russian Hill": 4
    },
    "Pacific Heights": {
        "Nob Hill": 8, "Embarcadero": 10, "The Castro": 16, "Haight-Ashbury": 11,
        "Union Square": 12, "North Beach": 9, "Chinatown": 11, "Golden Gate Park": 15,
        "Marina District": 6, "Russian Hill": 7
    },
    "Chinatown": {
        "Nob Hill": 9, "Embarcadero": 5, "The Castro": 22, "Haight-Ashbury": 19,
        "Union Square": 7, "North Beach": 3, "Pacific Heights": 10, "Golden Gate Park": 23,
        "Marina District": 12, "Russian Hill": 7
    },
    "Golden Gate Park": {
        "Nob Hill": 20, "Embarcadero": 25, "The Castro": 13, "Haight-Ashbury": 7,
        "Union Square": 22, "North Beach": 23, "Pacific Heights": 16, "Chinatown": 23,
        "Marina District": 16, "Russian Hill": 19
    },
    "Marina District": {
        "Nob Hill": 12, "Embarcadero": 14, "The Castro": 22, "Haight-Ashbury": 16,
        "Union Square": 16, "North Beach": 11, "Pacific Heights": 7, "Chinatown": 15,
        "Golden Gate Park": 18, "Russian Hill": 8
    },
    "Russian Hill": {
        "Nob Hill": 5, "Embarcadero": 8, "The Castro": 21, "Haight-Ashbury": 17,
        "Union Square": 10, "North Beach": 5, "Pacific Heights": 7, "Chinatown": 9,
        "Golden Gate Park": 21, "Marina District": 7
    }
}

# Friend data: name, location, available_start, available_end, min_duration
friends = [
    ("Mary", "Embarcadero", "20:00", "21:15", 75),
    ("Kenneth", "The Castro", "11:15", "19:15", 30),
    ("Joseph", "Haight-Ashbury", "20:00", "22:00", 120),
    ("Sarah", "Union Square", "11:45", "14:30", 90),
    ("Thomas", "North Beach", "19:15", "19:45", 15),
    ("Daniel", "Pacific Heights", "13:45", "20:30", 15),
    ("Richard", "Chinatown", "8:00", "18:45", 30),
    ("Mark", "Golden Gate Park", "17:30", "21:30", 120),
    ("David", "Marina District", "20:00", "21:00", 60),
    ("Karen", "Russian Hill", "13:15", "18:30", 120)
]

def calculate_schedule():
    current_location = "Nob Hill"
    current_time = time_to_minutes("9:00")
    itinerary = []
    remaining_friends = friends.copy()
    
    # Sort friends by earliest possible meeting time
    remaining_friends.sort(key=lambda x: time_to_minutes(x[2]))
    
    while remaining_friends:
        best_friend = None
        best_start = None
        best_end = None
        best_travel_time = None
        
        for friend in remaining_friends:
            name, location, avail_start, avail_end, min_duration = friend
            travel_time = travel_times[current_location][location]
            earliest_arrival = current_time + travel_time
            avail_start_min = time_to_minutes(avail_start)
            avail_end_min = time_to_minutes(avail_end)
            
            # Calculate possible meeting window
            meeting_start = max(earliest_arrival, avail_start_min)
            meeting_end = min(meeting_start + min_duration, avail_end_min)
            
            if meeting_end - meeting_start >= min_duration:
                if best_friend is None or meeting_start < best_start:
                    best_friend = friend
                    best_start = meeting_start
                    best_end = meeting_end
                    best_travel_time = travel_time
        
        if best_friend is None:
            break
            
        name, location, _, _, _ = best_friend
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": minutes_to_time(best_start),
            "end_time": minutes_to_time(best_end)
        })
        
        current_location = location
        current_time = best_end
        remaining_friends.remove(best_friend)
    
    return itinerary

itinerary = calculate_schedule()
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))