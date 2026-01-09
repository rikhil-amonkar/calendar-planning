from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = ["Financial District", "Chinatown", "Alamo Square", "Bayview", "Fisherman's Wharf"]
    
    # Travel times in minutes (from row to column)
    travel_times = {
        "Financial District": {
            "Financial District": 0,
            "Chinatown": 5,
            "Alamo Square": 17,
            "Bayview": 19,
            "Fisherman's Wharf": 10
        },
        "Chinatown": {
            "Financial District": 5,
            "Chinatown": 0,
            "Alamo Square": 17,
            "Bayview": 22,
            "Fisherman's Wharf": 8
        },
        "Alamo Square": {
            "Financial District": 17,
            "Chinatown": 16,
            "Alamo Square": 0,
            "Bayview": 16,
            "Fisherman's Wharf": 19
        },
        "Bayview": {
            "Financial District": 19,
            "Chinatown": 18,
            "Alamo Square": 16,
            "Bayview": 0,
            "Fisherman's Wharf": 25
        },
        "Fisherman's Wharf": {
            "Financial District": 11,
            "Chinatown": 12,
            "Alamo Square": 20,
            "Bayview": 26,
            "Fisherman's Wharf": 0
        }
    }
    
    # Friend constraints
    friends = {
        "Nancy": {
            "location": "Chinatown",
            "available_start": datetime.strptime("9:30", "%H:%M"),
            "available_end": datetime.strptime("13:30", "%H:%M"),
            "min_duration": 90  # minutes
        },
        "Mary": {
            "location": "Alamo Square",
            "available_start": datetime.strptime("7:00", "%H:%M"),
            "available_end": datetime.strptime("21:00", "%H:%M"),
            "min_duration": 75  # minutes
        },
        "Jessica": {
            "location": "Bayview",
            "available_start": datetime.strptime("11:15", "%H:%M"),
            "available_end": datetime.strptime("13:45", "%H:%M"),
            "min_duration": 45  # minutes
        },
        "Rebecca": {
            "location": "Fisherman's Wharf",
            "available_start": datetime.strptime("7:00", "%H:%M"),
            "available_end": datetime.strptime("8:30", "%H:%M"),
            "min_duration": 45  # minutes
        }
    }
    
    # Start time
    start_time = datetime.strptime("9:00", "%H:%M")
    current_location = "Financial District"
    
    # We can't meet Rebecca (available before we start)
    # Let's try different meeting orders to maximize the number of friends we can meet
    
    # Generate all possible meeting orders for the 3 friends
    possible_orders = [
        ["Nancy", "Mary", "Jessica"],
        ["Nancy", "Jessica", "Mary"],
        ["Mary", "Nancy", "Jessica"],
        ["Mary", "Jessica", "Nancy"],
        ["Jessica", "Nancy", "Mary"],
        ["Jessica", "Mary", "Nancy"]
    ]
    
    best_itinerary = []
    max_meetings = 0
    
    for order in possible_orders:
        itinerary = []
        current_time = start_time
        current_loc = "Financial District"
        meetings_achieved = []
        
        for friend_name in order:
            friend = friends[friend_name]
            
            # Calculate travel time to friend's location
            travel_time = travel_times[current_loc][friend["location"]]
            arrival_time = current_time + timedelta(minutes=travel_time)
            
            # Check if we can meet this friend
            # We need to arrive before their availability ends
            if arrival_time < friend["available_end"]:
                # Determine meeting start time
                meeting_start = max(arrival_time, friend["available_start"])
                
                # Check if we have enough time for the minimum duration
                if meeting_start + timedelta(minutes=friend["min_duration"]) <= friend["available_end"]:
                    # Use minimum duration for simplicity
                    meeting_end = meeting_start + timedelta(minutes=friend["min_duration"])
                    
                    # Add travel to itinerary
                    if current_loc != friend["location"]:
                        itinerary.append({
                            "action": "travel",
                            "location": friend["location"],
                            "person": None,
                            "start_time": current_time.strftime("%H:%M"),
                            "end_time": arrival_time.strftime("%H:%M")
                        })
                    
                    # Add meeting to itinerary
                    itinerary.append({
                        "action": "meet",
                        "location": friend["location"],
                        "person": friend_name,
                        "start_time": meeting_start.strftime("%H:%M"),
                        "end_time": meeting_end.strftime("%H:%M")
                    })
                    
                    meetings_achieved.append(friend_name)
                    current_time = meeting_end
                    current_loc = friend["location"]
        
        # Check if this order gives us more meetings
        if len(meetings_achieved) > max_meetings:
            max_meetings = len(meetings_achieved)
            best_itinerary = itinerary.copy()
    
    # If no meetings found in any order, try individual meetings
    if max_meetings == 0:
        # Try to meet at least Mary (widest availability)
        friend = friends["Mary"]
        travel_time = travel_times["Financial District"][friend["location"]]
        arrival_time = start_time + timedelta(minutes=travel_time)
        
        if arrival_time < friend["available_end"]:
            meeting_start = max(arrival_time, friend["available_start"])
            meeting_end = meeting_start + timedelta(minutes=friend["min_duration"])
            
            best_itinerary = [
                {
                    "action": "travel",
                    "location": friend["location"],
                    "person": None,
                    "start_time": start_time.strftime("%H:%M"),
                    "end_time": arrival_time.strftime("%H:%M")
                },
                {
                    "action": "meet",
                    "location": friend["location"],
                    "person": "Mary",
                    "start_time": meeting_start.strftime("%H:%M"),
                    "end_time": meeting_end.strftime("%H:%M")
                }
            ]
    
    # Output result
    result = {
        "itinerary": best_itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()