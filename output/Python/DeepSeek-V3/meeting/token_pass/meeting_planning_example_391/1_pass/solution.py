import json
import itertools
from collections import defaultdict

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Travel times in minutes: from_location, to_location
    travel = defaultdict(dict)
    
    travel["Sunset District"]["Alamo Square"] = 17
    travel["Sunset District"]["Russian Hill"] = 24
    travel["Sunset District"]["Presidio"] = 16
    travel["Sunset District"]["Financial District"] = 30
    
    travel["Alamo Square"]["Sunset District"] = 16
    travel["Alamo Square"]["Russian Hill"] = 13
    travel["Alamo Square"]["Presidio"] = 18
    travel["Alamo Square"]["Financial District"] = 17
    
    travel["Russian Hill"]["Sunset District"] = 23
    travel["Russian Hill"]["Alamo Square"] = 15
    travel["Russian Hill"]["Presidio"] = 14
    travel["Russian Hill"]["Financial District"] = 11
    
    travel["Presidio"]["Sunset District"] = 15
    travel["Presidio"]["Alamo Square"] = 18
    travel["Presidio"]["Russian Hill"] = 14
    travel["Presidio"]["Financial District"] = 23
    
    travel["Financial District"]["Sunset District"] = 31
    travel["Financial District"]["Alamo Square"] = 17
    travel["Financial District"]["Russian Hill"] = 10
    travel["Financial District"]["Presidio"] = 22
    
    # Friend data: name, location, window_start, window_end, min_duration
    friends = [
        {
            "name": "Kevin",
            "location": "Alamo Square",
            "window_start": time_to_minutes("8:15"),
            "window_end": time_to_minutes("21:30"),
            "min_duration": 75
        },
        {
            "name": "Kimberly",
            "location": "Russian Hill",
            "window_start": time_to_minutes("8:45"),
            "window_end": time_to_minutes("12:30"),
            "min_duration": 30
        },
        {
            "name": "Joseph",
            "location": "Presidio",
            "window_start": time_to_minutes("18:30"),
            "window_end": time_to_minutes("19:15"),
            "min_duration": 45
        },
        {
            "name": "Thomas",
            "location": "Financial District",
            "window_start": time_to_minutes("19:00"),
            "window_end": time_to_minutes("21:45"),
            "min_duration": 45
        }
    ]
    
    # Map name to friend index
    name_to_index = {f["name"]: i for i, f in enumerate(friends)}
    
    # Start location and time
    start_location = "Sunset District"
    start_time = time_to_minutes("9:00")
    
    best_count = 0
    best_total_duration = 0
    best_schedule = []
    best_itinerary = []
    
    # Try all subsets and permutations
    for r in range(1, len(friends) + 1):
        for subset in itertools.combinations([f["name"] for f in friends], r):
            for perm in itertools.permutations(subset):
                current_loc = start_location
                current_time = start_time
                feasible = True
                schedule = []
                total_duration = 0
                
                for name in perm:
                    idx = name_to_index[name]
                    f = friends[idx]
                    # Travel to friend's location
                    travel_time = travel[current_loc][f["location"]]
                    arrival = current_time + travel_time
                    # Start meeting at max(arrival, window_start)
                    start_meeting = max(arrival, f["window_start"])
                    # Check if we can meet min duration
                    if start_meeting + f["min_duration"] > f["window_end"]:
                        feasible = False
                        break
                    end_meeting = start_meeting + f["min_duration"]
                    schedule.append({
                        "name": name,
                        "location": f["location"],
                        "start": start_meeting,
                        "end": end_meeting,
                        "travel_time": travel_time
                    })
                    total_duration += f["min_duration"]
                    current_loc = f["location"]
                    current_time = end_meeting
                
                if feasible:
                    if len(perm) > best_count or (len(perm) == best_count and total_duration > best_total_duration):
                        best_count = len(perm)
                        best_total_duration = total_duration
                        best_schedule = schedule
                        best_itinerary = perm
    
    # Build output itinerary
    itinerary_json = []
    for s in best_schedule:
        itinerary_json.append({
            "action": "meet",
            "location": s["location"],
            "person": s["name"],
            "start_time": minutes_to_time(s["start"]),
            "end_time": minutes_to_time(s["end"])
        })
    
    result = {"itinerary": itinerary_json}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()