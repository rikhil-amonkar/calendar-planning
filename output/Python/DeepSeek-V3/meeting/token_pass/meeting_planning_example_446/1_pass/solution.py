import json
from itertools import permutations
from datetime import datetime, timedelta

# Travel times matrix (in minutes)
travel_times = {
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Bayview"): 26,
    ("Richmond District", "Union Square"): 21,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Chinatown"): 16,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Union Square"): 7,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Union Square"): 9,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Union Square"): 17,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Bayview"): 15,
}

# Friend data: name, location, window start, window end, min duration (minutes)
friends = [
    ("Kimberly", "Marina District", 13, 15, 16, 45, 15),
    ("Robert", "Chinatown", 12, 15, 20, 15, 15),
    ("Rebecca", "Financial District", 13, 15, 16, 45, 75),
    ("Margaret", "Bayview", 9, 30, 13, 30, 30),
    ("Kenneth", "Union Square", 19, 30, 21, 15, 75),
]

def time_to_minutes(hour, minute):
    return hour * 60 + minute

def minutes_to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def schedule_meetings(order):
    current_time = 9 * 60  # start at Richmond District 9:00
    current_loc = "Richmond District"
    itinerary = []
    met_count = 0
    
    for idx in order:
        name, loc, start_h, start_m, end_h, end_m, min_dur = friends[idx]
        travel = travel_times.get((current_loc, loc), float('inf'))
        arrival = current_time + travel
        window_start = time_to_minutes(start_h, start_m)
        window_end = time_to_minutes(end_h, end_m)
        
        if arrival > window_end:
            return None, 0  # can't meet
        
        start_meeting = max(arrival, window_start)
        if start_meeting + min_dur > window_end:
            return None, 0  # not enough time in window
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time_str(start_meeting),
            "end_time": minutes_to_time_str(start_meeting + min_dur)
        })
        met_count += 1
        current_time = start_meeting + min_dur
        current_loc = loc
    
    return itinerary, met_count

def main():
    best_met = 0
    best_itinerary = None
    
    # Try all permutations of 5 friends
    for perm in permutations(range(5)):
        itinerary, met_count = schedule_meetings(perm)
        if met_count > best_met:
            best_met = met_count
            best_itinerary = itinerary
    
    # Output best found
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()