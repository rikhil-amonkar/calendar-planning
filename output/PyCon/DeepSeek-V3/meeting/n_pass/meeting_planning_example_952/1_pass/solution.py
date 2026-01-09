import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = [
        "Bayview", "North Beach", "Fisherman's Wharf", "Haight-Ashbury", 
        "Nob Hill", "Golden Gate Park", "Union Square", "Alamo Square", 
        "Presidio", "Chinatown", "Pacific Heights"
    ]
    
    # Travel time matrix (in minutes)
    travel_times = {
        "Bayview": {
            "North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19,
            "Nob Hill": 20, "Golden Gate Park": 22, "Union Square": 18,
            "Alamo Square": 16, "Presidio": 32, "Chinatown": 19, "Pacific Heights": 23
        },
        "North Beach": {
            "Bayview": 25, "Fisherman's Wharf": 5, "Haight-Ashbury": 18,
            "Nob Hill": 7, "Golden Gate Park": 22, "Union Square": 7,
            "Alamo Square": 16, "Presidio": 17, "Chinatown": 6, "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Bayview": 26, "North Beach": 6, "Haight-Ashbury": 22,
            "Nob Hill": 11, "Golden Gate Park": 25, "Union Square": 13,
            "Alamo Square": 21, "Presidio": 17, "Chinatown": 12, "Pacific Heights": 12
        },
        "Haight-Ashbury": {
            "Bayview": 18, "North Beach": 19, "Fisherman's Wharf": 23,
            "Nob Hill": 15, "Golden Gate Park": 7, "Union Square": 19,
            "Alamo Square": 5, "Presidio": 15, "Chinatown": 19, "Pacific Heights": 12
        },
        "Nob Hill": {
            "Bayview": 19, "North Beach": 8, "Fisherman's Wharf": 10,
            "Haight-Ashbury": 13, "Golden Gate Park": 17, "Union Square": 7,
            "Alamo Square": 11, "Presidio": 17, "Chinatown": 6, "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Bayview": 23, "North Beach": 23, "Fisherman's Wharf": 24,
            "Haight-Ashbury": 7, "Nob Hill": 20, "Union Square": 22,
            "Alamo Square": 9, "Presidio": 11, "Chinatown": 23, "Pacific Heights": 16
        },
        "Union Square": {
            "Bayview": 15, "North Beach": 10, "Fisherman's Wharf": 15,
            "Haight-Ashbury": 18, "Nob Hill": 9, "Golden Gate Park": 22,
            "Alamo Square": 15, "Presidio": 24, "Chinatown": 7, "Pacific Heights": 15
        },
        "Alamo Square": {
            "Bayview": 16, "North Beach": 15, "Fisherman's Wharf": 19,
            "Haight-Ashbury": 5, "Nob Hill": 11, "Golden Gate Park": 9,
            "Union Square": 14, "Presidio": 17, "Chinatown": 15, "Pacific Heights": 10
        },
        "Presidio": {
            "Bayview": 31, "North Beach": 18, "Fisherman's Wharf": 19,
            "Haight-Ashbury": 15, "Nob Hill": 18, "Golden Gate Park": 12,
            "Union Square": 22, "Alamo Square": 19, "Chinatown": 21, "Pacific Heights": 11
        },
        "Chinatown": {
            "Bayview": 20, "North Beach": 3, "Fisherman's Wharf": 8,
            "Haight-Ashbury": 19, "Nob Hill": 9, "Golden Gate Park": 23,
            "Union Square": 7, "Alamo Square": 17, "Presidio": 19, "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Bayview": 22, "North Beach": 9, "Fisherman's Wharf": 13,
            "Haight-Ashbury": 11, "Nob Hill": 8, "Golden Gate Park": 15,
            "Union Square": 12, "Alamo Square": 10, "Presidio": 11, "Chinatown": 11
        }
    }
    
    # Friend constraints
    friends = [
        {"name": "Brian", "location": "North Beach", "start": datetime(2023, 1, 1, 13, 0), 
         "end": datetime(2023, 1, 1, 19, 0), "min_duration": 90},
        {"name": "Richard", "location": "Fisherman's Wharf", "start": datetime(2023, 1, 1, 11, 0), 
         "end": datetime(2023, 1, 1, 12, 45), "min_duration": 60},
        {"name": "Ashley", "location": "Haight-Ashbury", "start": datetime(2023, 1, 1, 15, 0), 
         "end": datetime(2023, 1, 1, 20, 30), "min_duration": 90},
        {"name": "Elizabeth", "location": "Nob Hill", "start": datetime(2023, 1, 1, 11, 45), 
         "end": datetime(2023, 1, 1, 18, 30), "min_duration": 75},
        {"name": "Jessica", "location": "Golden Gate Park", "start": datetime(2023, 1, 1, 20, 0), 
         "end": datetime(2023, 1, 1, 21, 45), "min_duration": 105},
        {"name": "Deborah", "location": "Union Square", "start": datetime(2023, 1, 1, 17, 30), 
         "end": datetime(2023, 1, 1, 22, 0), "min_duration": 60},
        {"name": "Kimberly", "location": "Alamo Square", "start": datetime(2023, 1, 1, 17, 30), 
         "end": datetime(2023, 1, 1, 21, 15), "min_duration": 45},
        {"name": "Matthew", "location": "Presidio", "start": datetime(2023, 1, 1, 8, 15), 
         "end": datetime(2023, 1, 1, 9, 0), "min_duration": 15},
        {"name": "Kenneth", "location": "Chinatown", "start": datetime(2023, 1, 1, 13, 45), 
         "end": datetime(2023, 1, 1, 19, 30), "min_duration": 105},
        {"name": "Anthony", "location": "Pacific Heights", "start": datetime(2023, 1, 1, 14, 15), 
         "end": datetime(2023, 1, 1, 16, 0), "min_duration": 30}
    ]
    
    # Start time
    current_time = datetime(2023, 1, 1, 9, 0)
    current_location = "Bayview"
    itinerary = []
    
    # Sort friends by availability and try to meet as many as possible
    # Simple greedy algorithm: meet friends in chronological order of their availability
    available_friends = sorted(friends, key=lambda x: x["start"])
    
    for friend in available_friends:
        # Calculate travel time
        travel_time = travel_times[current_location][friend["location"]]
        
        # Calculate arrival time
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        # Check if we can meet this friend
        if arrival_time <= friend["end"]:
            # Determine meeting start time (max of arrival time and friend's start time)
            meeting_start = max(arrival_time, friend["start"])
            
            # Calculate meeting end time
            meeting_end = meeting_start + timedelta(minutes=friend["min_duration"])
            
            # Check if meeting fits within friend's availability
            if meeting_end <= friend["end"]:
                # Add to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": meeting_start.strftime("%H:%M"),
                    "end_time": meeting_end.strftime("%H:%M")
                })
                
                # Update current time and location
                current_time = meeting_end
                current_location = friend["location"]
    
    # Output result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()