import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def main():
    # Input parameters
    arrival_location = "Alamo Square"
    arrival_time = parse_time("9:00")
    
    # Friend's availability
    friend_name = "Timothy"
    friend_location = "Richmond District"
    friend_window_start = parse_time("20:45")
    friend_window_end = parse_time("21:30")
    required_duration = timedelta(minutes=45)
    
    # Travel times
    travel_times = {
        ("Alamo Square", "Richmond District"): timedelta(minutes=12),
        ("Richmond District", "Alamo Square"): timedelta(minutes=13)
    }
    
    # Calculate possible meeting time
    travel_to_friend = travel_times[(arrival_location, friend_location)]
    earliest_arrival = arrival_time + travel_to_friend
    
    # Check if we can make it during friend's window
    meeting_start = max(earliest_arrival, friend_window_start)
    meeting_end = meeting_start + required_duration
    
    itinerary = []
    
    if meeting_end <= friend_window_end:
        # Add travel to friend
        itinerary.append({
            "action": "travel",
            "from": arrival_location,
            "to": friend_location,
            "start_time": format_time(arrival_time),
            "end_time": format_time(earliest_arrival)
        })
        
        # Add meeting with friend
        itinerary.append({
            "action": "meet",
            "location": friend_location,
            "person": friend_name,
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
        
        # Add return travel
        travel_home = travel_times[(friend_location, arrival_location)]
        home_arrival = meeting_end + travel_home
        itinerary.append({
            "action": "travel",
            "from": friend_location,
            "to": arrival_location,
            "start_time": format_time(meeting_end),
            "end_time": format_time(home_arrival)
        })
    else:
        # Can't meet friend
        itinerary.append({
            "action": "note",
            "message": "Cannot meet Timothy given constraints"
        })
    
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()