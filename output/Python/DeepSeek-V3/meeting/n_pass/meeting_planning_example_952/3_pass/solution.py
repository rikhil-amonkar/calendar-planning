import json
from itertools import permutations

# Travel times dictionary (same as before)
travel_times = {
    "Bayview": {
        "North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19,
        "Nob Hill": 20, "Golden Gate Park": 22, "Union Square": 18,
        "Alamo Square": 16, "Presidio": 32, "Chinatown": 19, "Pacific Heights": 23
    },
    # ... (rest of travel_times remains the same)
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