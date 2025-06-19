import itertools
import json

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        "Bayview": {
            "North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19, "Nob Hill": 20,
            "Golden Gate Park": 22, "Union Square": 18, "Alamo Square": 16, "Presidio": 32,
            "Chinatown": 19, "Pacific Heights": 23
        },
        "North Beach": {
            "Bayview": 25, "Fisherman's Wharf": 5, "Haight-Ashbury": 18, "Nob Hill": 7,
            "Golden Gate Park": 22, "Union Square": 7, "Alamo Square": 16, "Presidio": 17,
            "Chinatown": 6, "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Bayview": 26, "North Beach": 6, "Haight-Ashbury": 22, "Nob Hill": 11,
            "Golden Gate Park": 25, "Union Square": 13, "Alamo Square": 21, "Presidio": 17,
            "Chinatown": 12, "Pacific Heights": 12
        },
        "Haight-Ashbury": {
            "Bayview": 18, "North Beach": 19, "Fisherman's Wharf": 23, "Nob Hill": 15,
            "Golden Gate Park": 7, "Union Square": 19, "Alamo Square": 5, "Presidio": 15,
            "Chinatown": 19, "Pacific Heights": 12
        },
        "Nob Hill": {
            "Bayview": 19, "North Beach": 8, "Fisherman's Wharf": 10, "Haight-Ashbury": 13,
            "Golden Gate Park": 17, "Union Square": 7, "Alamo Square": 11, "Presidio": 17,
            "Chinatown": 6, "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Bayview": 23, "North Beach": 23, "Fisherman's Wharf": 24, "Haight-Ashbury": 7,
            "Nob Hill": 20, "Union Square": 22, "Alamo Square": 9, "Presidio": 11,
            "Chinatown": 23, "Pacific Heights": 16
        },
        "Union Square": {
            "Bayview": 15, "North Beach": 10, "Fisherman's Wharf": 15, "Haight-Ashbury": 18,
            "Nob Hill": 9, "Golden Gate Park": 22, "Alamo Square": 15, "Presidio": 24,
            "Chinatown": 7, "Pacific Heights": 15
        },
        "Alamo Square": {
            "Bayview": 16, "North Beach": 15, "Fisherman's Wharf": 19, "Haight-Ashbury": 5,
            "Nob Hill": 11, "Golden Gate Park": 9, "Union Square": 14, "Presidio": 17,
            "Chinatown": 15, "Pacific Heights": 10
        },
        "Presidio": {
            "Bayview": 31, "North Beach": 18, "Fisherman's Wharf": 19, "Haight-Ashbury": 15,
            "Nob Hill": 18, "Golden Gate Park": 12, "Union Square": 22, "Alamo Square": 19,
            "Chinatown": 21, "Pacific Heights": 11
        },
        "Chinatown": {
            "Bayview": 20, "North Beach": 3, "Fisherman's Wharf": 8, "Haight-Ashbury": 19,
            "Nob Hill": 9, "Golden Gate Park": 23, "Union Square": 7, "Alamo Square": 17,
            "Presidio": 19, "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Bayview": 22, "North Beach": 9, "Fisherman's Wharf": 13, "Haight-Ashbury": 11,
            "Nob Hill": 8, "Golden Gate Park": 15, "Union Square": 12, "Alamo Square": 10,
            "Presidio": 11, "Chinatown": 11
        }
    }
    
    # Define friends' data in minutes (excluding Matthew)
    friends_data = [
        {"name": "Brian", "location": "North Beach", "start": 13*60, "end": 19*60, "min_duration": 90},
        {"name": "Richard", "location": "Fisherman's Wharf", "start": 11*60, "end": 12*60+45, "min_duration": 60},
        {"name": "Ashley", "location": "Haight-Ashbury", "start": 15*60, "end": 20*60+30, "min_duration": 90},
        {"name": "Elizabeth", "location": "Nob Hill", "start": 11*60+45, "end": 18*60+30, "min_duration": 75},
        {"name": "Jessica", "location": "Golden Gate Park", "start": 20*60, "end": 21*60+45, "min_duration": 105},
        {"name": "Deborah", "location": "Union Square", "start": 17*60+30, "end": 22*60, "min_duration": 60},
        {"name": "Kimberly", "location": "Alamo Square", "start": 17*60+30, "end": 21*60+15, "min_duration": 45},
        {"name": "Kenneth", "location": "Chinatown", "start": 13*60+45, "end": 19*60+30, "min_duration": 105},
        {"name": "Anthony", "location": "Pacific Heights", "start": 14*60+15, "end": 16*60, "min_duration": 30}
    ]
    
    # Generate all permutations of the friends
    permutations = list(itertools.permutations(friends_data))
    best_count = 0
    best_schedule = None
    
    # Start time in minutes (9:00 AM)
    start_time = 9 * 60
    
    for perm in permutations:
        current_time = start_time
        current_location = "Bayview"
        itinerary = []
        valid = True
        
        for friend in perm:
            # Skip Matthew is not included
            if current_location == friend["location"]:
                travel = 0
            else:
                travel = travel_times[current_location][friend["location"]]
            
            arrival_time = current_time + travel
            meeting_start = max(arrival_time, friend["start"])
            meeting_end = meeting_start + friend["min_duration"]
            
            # Check if meeting can be scheduled within friend's availability
            if meeting_end <= friend["end"]:
                itinerary.append({
                    "name": friend["name"],
                    "location": friend["location"],
                    "start": meeting_start,
                    "end": meeting_end
                })
                current_time = meeting_end
                current_location = friend["location"]
            else:
                # Skip friend if not feasible
                continue
            
            # Early termination if current_time exceeds the latest possible meeting end
            if current_time > 22 * 60:  # 10:00 PM
                break
        
        # Update best schedule if this permutation has more meetings
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_schedule = itinerary
    
    # Format the best schedule for output
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"
    
    output_itinerary = []
    for meeting in best_schedule:
        output_itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": format_time(meeting["start"]),
            "end_time": format_time(meeting["end"])
        })
    
    # Output as JSON
    result = {"itinerary": output_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()