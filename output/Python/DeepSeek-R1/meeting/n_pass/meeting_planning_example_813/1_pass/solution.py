import itertools
import json

def main():
    # Travel times dictionary
    travel_times = {
        "Marina District": {
            "Embarcadero": 14,
            "Bayview": 27,
            "Union Square": 16,
            "Chinatown": 15,
            "Golden Gate Park": 18,
            "Financial District": 17,
            "Haight-Ashbury": 16,
            "Mission District": 20
        },
        "Embarcadero": {
            "Marina District": 12,
            "Bayview": 21,
            "Union Square": 10,
            "Chinatown": 7,
            "Golden Gate Park": 25,
            "Financial District": 5,
            "Haight-Ashbury": 21,
            "Mission District": 20
        },
        "Bayview": {
            "Marina District": 27,
            "Embarcadero": 19,
            "Union Square": 18,
            "Chinatown": 19,
            "Golden Gate Park": 22,
            "Financial District": 19,
            "Haight-Ashbury": 19,
            "Mission District": 13
        },
        "Union Square": {
            "Marina District": 18,
            "Embarcadero": 11,
            "Bayview": 15,
            "Chinatown": 7,
            "Golden Gate Park": 22,
            "Financial District": 9,
            "Haight-Ashbury": 18,
            "Mission District": 14
        },
        "Chinatown": {
            "Marina District": 12,
            "Embarcadero": 5,
            "Bayview": 20,
            "Union Square": 7,
            "Golden Gate Park": 23,
            "Financial District": 5,
            "Haight-Ashbury": 19,
            "Mission District": 17
        },
        "Golden Gate Park": {
            "Marina District": 16,
            "Embarcadero": 25,
            "Bayview": 23,
            "Union Square": 22,
            "Chinatown": 23,
            "Financial District": 26,
            "Haight-Ashbury": 7,
            "Mission District": 17
        },
        "Financial District": {
            "Marina District": 15,
            "Embarcadero": 4,
            "Bayview": 19,
            "Union Square": 9,
            "Chinatown": 5,
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Mission District": 17
        },
        "Haight-Ashbury": {
            "Marina District": 17,
            "Embarcadero": 20,
            "Bayview": 18,
            "Union Square": 19,
            "Chinatown": 19,
            "Golden Gate Park": 7,
            "Financial District": 21,
            "Mission District": 11
        },
        "Mission District": {
            "Marina District": 19,
            "Embarcadero": 19,
            "Bayview": 14,
            "Union Square": 15,
            "Chinatown": 16,
            "Golden Gate Park": 17,
            "Financial District": 15,
            "Haight-Ashbury": 12
        }
    }
    
    # Friends list (without Elizabeth since it's impossible to meet her)
    friends = [
        {"name": "Joshua", "location": "Embarcadero", "start": 9*60+45, "end": 18*60, "duration": 105},
        {"name": "Jeffrey", "location": "Bayview", "start": 9*60+45, "end": 20*60+15, "duration": 75},
        {"name": "Charles", "location": "Union Square", "start": 10*60+45, "end": 20*60+15, "duration": 120},
        {"name": "Joseph", "location": "Chinatown", "start": 7*60, "end": 15*60+30, "duration": 60},
        {"name": "Matthew", "location": "Golden Gate Park", "start": 11*60, "end": 19*60+30, "duration": 45},
        {"name": "Carol", "location": "Financial District", "start": 10*60+45, "end": 11*60+15, "duration": 15},
        {"name": "Paul", "location": "Haight-Ashbury", "start": 19*60+15, "end": 20*60+30, "duration": 15},
        {"name": "Rebecca", "location": "Mission District", "start": 17*60, "end": 21*60+45, "duration": 45}
    ]
    
    # Initialize variables
    best_count = 0
    best_schedule = None
    found_full = False
    
    # Generate all permutations of friends
    for perm in itertools.permutations(friends):
        if found_full:
            break
        current_time = 540  # 9:00 AM in minutes
        current_location = "Marina District"
        schedule = []
        
        for friend in perm:
            # Get travel time from current location to friend's location
            travel_time = travel_times[current_location][friend["location"]]
            arrival_time = current_time + travel_time
            
            # Skip if we arrive after the friend's window ends
            if arrival_time > friend["end"]:
                continue
                
            # Calculate meeting start and end times
            start_meeting = max(arrival_time, friend["start"])
            end_meeting = start_meeting + friend["duration"]
            
            # Check if meeting can be completed within friend's window
            if end_meeting <= friend["end"]:
                # Schedule the meeting
                schedule.append({
                    "friend": friend,
                    "start": start_meeting,
                    "end": end_meeting
                })
                current_time = end_meeting
                current_location = friend["location"]
            else:
                continue
        
        count = len(schedule)
        if count > best_count:
            best_count = count
            best_schedule = schedule
            if best_count == 8:  # Found a schedule meeting all friends
                found_full = True
                break
    
    # Format the best schedule to the required output
    itinerary = []
    for meeting in best_schedule:
        # Convert minutes to time string (H:MM format)
        start_hour = meeting['start'] // 60
        start_minute = meeting['start'] % 60
        end_hour = meeting['end'] // 60
        end_minute = meeting['end'] % 60
        
        start_str = f"{start_hour}:{start_minute:02d}"
        end_str = f"{end_hour}:{end_minute:02d}"
        
        itinerary.append({
            "action": "meet",
            "location": meeting['friend']['location'],
            "person": meeting['friend']['name'],
            "start_time": start_str,
            "end_time": end_str
        })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()