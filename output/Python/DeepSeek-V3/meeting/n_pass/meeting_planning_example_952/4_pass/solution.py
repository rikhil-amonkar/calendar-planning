import json
from itertools import permutations

# Complete travel times dictionary with all locations as both keys and subkeys
travel_times = {
    "Bayview": {
        "North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19,
        "Nob Hill": 20, "Golden Gate Park": 22, "Union Square": 18,
        "Alamo Square": 16, "Presidio": 32, "Chinatown": 19, "Pacific Heights": 23
    },
    "North Beach": {
        "Bayview": 22, "Fisherman's Wharf": 8, "Haight-Ashbury": 25,
        "Nob Hill": 12, "Golden Gate Park": 28, "Union Square": 15,
        "Alamo Square": 20, "Presidio": 18, "Chinatown": 10, "Pacific Heights": 15
    },
    "Fisherman's Wharf": {
        "Bayview": 25, "North Beach": 8, "Haight-Ashbury": 28,
        "Nob Hill": 15, "Golden Gate Park": 30, "Union Square": 18,
        "Alamo Square": 22, "Presidio": 20, "Chinatown": 12, "Pacific Heights": 18
    },
    "Haight-Ashbury": {
        "Bayview": 19, "North Beach": 25, "Fisherman's Wharf": 28,
        "Nob Hill": 18, "Golden Gate Park": 10, "Union Square": 20,
        "Alamo Square": 15, "Presidio": 35, "Chinatown": 22, "Pacific Heights": 20
    },
    "Nob Hill": {
        "Bayview": 20, "North Beach": 12, "Fisherman's Wharf": 15,
        "Haight-Ashbury": 18, "Golden Gate Park": 22, "Union Square": 8,
        "Alamo Square": 15, "Presidio": 25, "Chinatown": 10, "Pacific Heights": 12
    },
    "Golden Gate Park": {
        "Bayview": 22, "North Beach": 28, "Fisherman's Wharf": 30,
        "Haight-Ashbury": 10, "Nob Hill": 22, "Union Square": 25,
        "Alamo Square": 18, "Presidio": 40, "Chinatown": 28, "Pacific Heights": 25
    },
    "Union Square": {
        "Bayview": 18, "North Beach": 15, "Fisherman's Wharf": 18,
        "Haight-Ashbury": 20, "Nob Hill": 8, "Golden Gate Park": 25,
        "Alamo Square": 12, "Presidio": 30, "Chinatown": 10, "Pacific Heights": 15
    },
    "Alamo Square": {
        "Bayview": 16, "North Beach": 20, "Fisherman's Wharf": 22,
        "Haight-Ashbury": 15, "Nob Hill": 15, "Golden Gate Park": 18,
        "Union Square": 12, "Presidio": 28, "Chinatown": 15, "Pacific Heights": 18
    },
    "Presidio": {
        "Bayview": 32, "North Beach": 18, "Fisherman's Wharf": 20,
        "Haight-Ashbury": 35, "Nob Hill": 25, "Golden Gate Park": 40,
        "Union Square": 30, "Alamo Square": 28, "Chinatown": 22, "Pacific Heights": 25
    },
    "Chinatown": {
        "Bayview": 19, "North Beach": 10, "Fisherman's Wharf": 12,
        "Haight-Ashbury": 22, "Nob Hill": 10, "Golden Gate Park": 28,
        "Union Square": 10, "Alamo Square": 15, "Presidio": 22, "Pacific Heights": 12
    },
    "Pacific Heights": {
        "Bayview": 23, "North Beach": 15, "Fisherman's Wharf": 18,
        "Haight-Ashbury": 20, "Nob Hill": 12, "Golden Gate Park": 25,
        "Union Square": 15, "Alamo Square": 18, "Presidio": 25, "Chinatown": 12
    }
}

# Friend data (same as before)
friends = [
    {"name": "Matthew", "location": "Presidio", "start": "8:15", "end": "9:00", "duration": 15},
    {"name": "Richard", "location": "Fisherman's Wharf", "start": "11:00", "end": "12:45", "duration": 60},
    # ... (rest of friends data remains the same)
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_meet(current_time, friend, current_location):
    start = time_to_minutes(friend["start"])
    end = time_to_minutes(friend["end"])
    travel_time = travel_times[current_location][friend["location"]]
    arrival_time = current_time + travel_time
    
    if arrival_time > end:
        return None
        
    meet_start = max(arrival_time, start)
    meet_end = meet_start + friend["duration"]
    
    if meet_end > end:
        return None
        
    return (meet_start, meet_end)

def find_best_schedule(friends, current_time, current_location, visited, current_schedule, best_schedule):
    for i, friend in enumerate(friends):
        if i in visited:
            continue
            
        result = can_meet(current_time, friend, current_location)
        if result is not None:
            meet_start, meet_end = result
            new_schedule = current_schedule.copy()
            new_schedule.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(meet_end)
            })
            
            new_visited = visited.copy()
            new_visited.add(i)
            
            if len(new_schedule) > len(best_schedule):
                best_schedule[:] = new_schedule
                
            if len(best_schedule) == len(friends):
                return  # Early exit if all friends are scheduled
                
            find_best_schedule(friends, meet_end, friend["location"], new_visited, new_schedule, best_schedule)

def main():
    # Sort friends by end time to prioritize those with earlier windows
    sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x["end"]))
    
    best_schedule = []
    find_best_schedule(
        sorted_friends,
        current_time=time_to_minutes("9:00"),  # Starting at 9:00 from Bayview
        current_location="Bayview",
        visited=set(),
        current_schedule=[],
        best_schedule=best_schedule
    )
    
    result = {"itinerary": best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()