import itertools
import json

def main():
    # Define travel times between locations (in minutes)
    travel_times = {
        "Bayview": {
            "Nob Hill": 20, "Union Square": 17, "Chinatown": 18, "The Castro": 20,
            "Presidio": 31, "Pacific Heights": 23, "Russian Hill": 23
        },
        "Nob Hill": {
            "Bayview": 19, "Union Square": 7, "Chinatown": 6, "The Castro": 17,
            "Presidio": 17, "Pacific Heights": 8, "Russian Hill": 5
        },
        "Union Square": {
            "Bayview": 15, "Nob Hill": 9, "Chinatown": 7, "The Castro": 19,
            "Presidio": 24, "Pacific Heights": 15, "Russian Hill": 13
        },
        "Chinatown": {
            "Bayview": 22, "Nob Hill": 8, "Union Square": 7, "The Castro": 22,
            "Presidio": 19, "Pacific Heights": 10, "Russian Hill": 7
        },
        "The Castro": {
            "Bayview": 19, "Nob Hill": 16, "Union Square": 19, "Chinatown": 20,
            "Presidio": 20, "Pacific Heights": 16, "Russian Hill": 18
        },
        "Presidio": {
            "Bayview": 31, "Nob Hill": 18, "Union Square": 22, "Chinatown": 21,
            "The Castro": 21, "Pacific Heights": 11, "Russian Hill": 14
        },
        "Pacific Heights": {
            "Bayview": 22, "Nob Hill": 8, "Union Square": 12, "Chinatown": 11,
            "The Castro": 16, "Presidio": 11, "Russian Hill": 7
        },
        "Russian Hill": {
            "Bayview": 23, "Nob Hill": 5, "Union Square": 11, "Chinatown": 9,
            "The Castro": 21, "Presidio": 14, "Pacific Heights": 7
        }
    }
    
    # Define friends with their constraints (times in minutes from midnight)
    friends = [
        {"name": "Paul", "location": "Nob Hill", "start_avail": 16*60+15, "end_avail": 21*60+15, "min_duration": 60},
        {"name": "Carol", "location": "Union Square", "start_avail": 18*60, "end_avail": 20*60+15, "min_duration": 120},
        {"name": "Patricia", "location": "Chinatown", "start_avail": 20*60, "end_avail": 21*60+30, "min_duration": 75},
        {"name": "Karen", "location": "The Castro", "start_avail": 17*60, "end_avail": 19*60, "min_duration": 45},
        {"name": "Nancy", "location": "Presidio", "start_avail": 11*60+45, "end_avail": 22*60, "min_duration": 30},
        {"name": "Jeffrey", "location": "Pacific Heights", "start_avail": 20*60, "end_avail": 20*60+45, "min_duration": 45},
        {"name": "Matthew", "location": "Russian Hill", "start_avail": 15*60+45, "end_avail": 21*60+45, "min_duration": 75}
    ]
    
    # Generate all permutations of friends
    all_permutations = list(itertools.permutations(friends))
    best_count = 0
    best_itinerary = None
    
    # Function to format minutes to time string (H:MM)
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"
    
    # Simulate each permutation
    for perm in all_permutations:
        current_location = "Bayview"
        current_time = 540  # 9:00 AM
        itinerary = []
        
        for friend in perm:
            travel_time = travel_times[current_location][friend["location"]]
            arrival_time = current_time + travel_time
            start_time = max(arrival_time, friend["start_avail"])
            end_time = start_time + friend["min_duration"]
            
            if end_time <= friend["end_avail"]:
                itinerary.append({
                    "friend": friend,
                    "start": start_time,
                    "end": end_time
                })
                current_location = friend["location"]
                current_time = end_time
        
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary
    
    # Format the best itinerary for output
    formatted_itinerary = []
    for meeting in best_itinerary:
        friend = meeting["friend"]
        formatted_itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": format_time(meeting["start"]),
            "end_time": format_time(meeting["end"])
        })
    
    result = {"itinerary": formatted_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()