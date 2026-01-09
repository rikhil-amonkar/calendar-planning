import json
from datetime import datetime, timedelta

def main():
    # Define locations and travel times
    locations = [
        "Presidio", "Fisherman's Wharf", "Alamo Square", "Financial District",
        "Union Square", "Sunset District", "Embarcadero", "Golden Gate Park",
        "Chinatown", "Richmond District"
    ]
    
    # Create travel time matrix
    travel_times = {
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Richmond District"): 11,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Richmond District"): 21,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Richmond District"): 20,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Richmond District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Richmond District"): 21,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Richmond District"): 20,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Chinatown"): 20,
    }
    
    # Friend constraints
    friends = [
        {"name": "Jeffrey", "location": "Fisherman's Wharf", "available_start": "10:15", "available_end": "13:00", "min_duration": 90},
        {"name": "Ronald", "location": "Alamo Square", "available_start": "7:45", "available_end": "14:45", "min_duration": 120},
        {"name": "Jason", "location": "Financial District", "available_start": "10:45", "available_end": "16:00", "min_duration": 105},
        {"name": "Melissa", "location": "Union Square", "available_start": "17:45", "available_end": "18:15", "min_duration": 15},
        {"name": "Elizabeth", "location": "Sunset District", "available_start": "14:45", "available_end": "17:30", "min_duration": 105},
        {"name": "Margaret", "location": "Embarcadero", "available_start": "13:15", "available_end": "19:00", "min_duration": 90},
        {"name": "George", "location": "Golden Gate Park", "available_start": "19:00", "available_end": "22:00", "min_duration": 75},
        {"name": "Richard", "location": "Chinatown", "available_start": "9:30", "available_end": "21:00", "min_duration": 15},
        {"name": "Laura", "location": "Richmond District", "available_start": "9:45", "available_end": "18:00", "min_duration": 60}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, "%H:%M")
        base_time = datetime.strptime("9:00", "%H:%M")
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime("9:00", "%H:%M")
        new_time = base_time + timedelta(minutes=minutes)
        return new_time.strftime("%H:%M").lstrip("0")
    
    # Convert friends data to use minutes
    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["available_start"])
        friend["end_min"] = time_to_minutes(friend["available_end"])
    
    # Greedy scheduling algorithm
    def schedule_meetings():
        itinerary = []
        current_time = 0  # Start at 9:00
        current_location = "Presidio"  # Starting location
        
        # Sort friends by end time (earlier first) to prioritize those with tighter windows
        sorted_friends = sorted(friends, key=lambda x: x["end_min"])
        
        scheduled = [False] * len(sorted_friends)
        
        while True:
            best_friend = None
            best_start = None
            best_end = None
            
            # Find the best next meeting
            for i, friend in enumerate(sorted_friends):
                if scheduled[i]:
                    continue
                
                # Calculate travel time to this friend
                travel_time = travel_times.get((current_location, friend["location"]), 30)
                
                # Earliest possible start time considering travel
                earliest_start = current_time + travel_time
                
                # Check if we can schedule within friend's availability
                if earliest_start <= friend["end_min"] - friend["min_duration"]:
                    # Start at the later of: earliest possible or friend's available start
                    start_time = max(earliest_start, friend["start_min"])
                    end_time = start_time + friend["min_duration"]
                    
                    # Check if this fits within friend's availability
                    if end_time <= friend["end_min"]:
                        # Prefer friends we can meet sooner
                        if best_friend is None or start_time < best_start:
                            best_friend = i
                            best_start = start_time
                            best_end = end_time
            
            if best_friend is None:
                break  # No more meetings can be scheduled
            
            # Schedule the meeting
            friend = sorted_friends[best_friend]
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(best_start),
                "end_time": minutes_to_time(best_end)
            })
            
            scheduled[best_friend] = True
            current_time = best_end
            current_location = friend["location"]
        
        return itinerary
    
    # Generate itinerary
    itinerary = schedule_meetings()
    
    # Output result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()