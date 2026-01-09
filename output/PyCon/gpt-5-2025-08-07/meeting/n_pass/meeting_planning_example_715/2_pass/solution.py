import json
from datetime import datetime, timedelta

def main():
    # Define locations
    locations = [
        "Presidio", "Marina District", "The Castro", "Fisherman's Wharf", 
        "Bayview", "Pacific Heights", "Mission District", "Alamo Square", "Golden Gate Park"
    ]
    
    # Travel time matrix (in minutes)
    travel_times = {
        "Presidio": {"Marina District": 11, "The Castro": 21, "Fisherman's Wharf": 19, 
                    "Bayview": 31, "Pacific Heights": 11, "Mission District": 26, 
                    "Alamo Square": 19, "Golden Gate Park": 12},
        "Marina District": {"Presidio": 10, "The Castro": 22, "Fisherman's Wharf": 10, 
                           "Bayview": 27, "Pacific Heights": 7, "Mission District": 20, 
                           "Alamo Square": 15, "Golden Gate Park": 18},
        "The Castro": {"Presidio": 20, "Marina District": 21, "Fisherman's Wharf": 24, 
                      "Bayview": 19, "Pacific Heights": 16, "Mission District": 7, 
                      "Alamo Square": 8, "Golden Gate Park": 11},
        "Fisherman's Wharf": {"Presidio": 17, "Marina District": 9, "The Castro": 27, 
                             "Bayview": 26, "Pacific Heights": 12, "Mission District": 22, 
                             "Alamo Square": 21, "Golden Gate Park": 25},
        "Bayview": {"Presidio": 32, "Marina District": 27, "The Castro": 19, 
                   "Fisherman's Wharf": 25, "Pacific Heights": 23, "Mission District": 13, 
                   "Alamo Square": 16, "Golden Gate Park": 22},
        "Pacific Heights": {"Presidio": 11, "Marina District": 6, "The Castro": 16, 
                           "Fisherman's Wharf": 13, "Bayview": 22, "Mission District": 15, 
                           "Alamo Square": 10, "Golden Gate Park": 15},
        "Mission District": {"Presidio": 25, "Marina District": 19, "The Castro": 7, 
                            "Fisherman's Wharf": 22, "Bayview": 14, "Pacific Heights": 16, 
                            "Alamo Square": 11, "Golden Gate Park": 17},
        "Alamo Square": {"Presidio": 17, "Marina District": 15, "The Castro": 8, 
                        "Fisherman's Wharf": 19, "Bayview": 16, "Pacific Heights": 10, 
                        "Mission District": 10, "Golden Gate Park": 9},
        "Golden Gate Park": {"Presidio": 11, "Marina District": 16, "The Castro": 13, 
                            "Fisherman's Wharf": 24, "Bayview": 23, "Pacific Heights": 16, 
                            "Mission District": 17, "Alamo Square": 9}
    }
    
    # Friend constraints
    friends = {
        "Amanda": {"location": "Marina District", "start": "14:45", "end": "19:30", "min_duration": 105},
        "Melissa": {"location": "The Castro", "start": "9:30", "end": "17:00", "min_duration": 30},
        "Jeffrey": {"location": "Fisherman's Wharf", "start": "12:45", "end": "18:45", "min_duration": 120},
        "Matthew": {"location": "Bayview", "start": "10:15", "end": "13:15", "min_duration": 30},
        "Nancy": {"location": "Pacific Heights", "start": "17:00", "end": "21:30", "min_duration": 105},
        "Karen": {"location": "Mission District", "start": "17:30", "end": "20:30", "min_duration": 105},
        "Robert": {"location": "Alamo Square", "start": "11:15", "end": "17:30", "min_duration": 120},
        "Joseph": {"location": "Golden Gate Park", "start": "8:30", "end": "21:15", "min_duration": 105}
    }
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, "%H:%M")
        base_time = datetime.strptime("9:00", "%H:%M")
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime("9:00", "%H:%M")
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime("%H:%M")
    
    # Convert friend data to minutes
    friend_data = []
    for name, info in friends.items():
        friend_data.append({
            "name": name,
            "location": info["location"],
            "start_min": time_to_minutes(info["start"]),
            "end_min": time_to_minutes(info["end"]),
            "min_duration": info["min_duration"]
        })
    
    # Sort friends by end time (earlier end times first)
    friend_data.sort(key=lambda x: x["end_min"])
    
    # Greedy scheduling algorithm
    schedule = []
    current_time = 0  # Start at 9:00 from Presidio
    current_location = "Presidio"
    
    for friend in friend_data:
        # Calculate earliest possible start time considering travel
        if schedule:
            travel_time = travel_times[current_location][friend["location"]]
            earliest_start = current_time + travel_time
        else:
            # First meeting - travel from Presidio
            travel_time = travel_times["Presidio"][friend["location"]]
            earliest_start = travel_time
        
        # Adjust start time to fit within friend's availability
        actual_start = max(earliest_start, friend["start_min"])
        
        # Check if we can schedule this meeting
        if actual_start + friend["min_duration"] <= friend["end_min"]:
            # Schedule for minimum duration
            duration = friend["min_duration"]
            end_time = actual_start + duration
            
            # Try to extend duration if possible
            max_possible_duration = friend["end_min"] - actual_start
            # Check if extending would conflict with next friends
            # For simplicity, we'll use minimum duration for now
            # This could be optimized further
            
            schedule.append({
                "friend": friend["name"],
                "location": friend["location"],
                "start": actual_start,
                "end": end_time,
                "duration": duration
            })
            
            current_time = end_time
            current_location = friend["location"]
    
    # Build itinerary
    itinerary = []
    
    if schedule:
        # Add travel from Presidio to first meeting
        first_meeting = schedule[0]
        travel_time = travel_times["Presidio"][first_meeting["location"]]
        
        itinerary.append({
            "action": "travel",
            "location": first_meeting["location"],
            "person": "",
            "start_time": minutes_to_time(0),
            "end_time": minutes_to_time(travel_time)
        })
        
        # Add meetings and travel between them
        for i, meeting in enumerate(schedule):
            # Add meeting
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["friend"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
            
            # Add travel to next meeting if there is one
            if i < len(schedule) - 1:
                next_meeting = schedule[i + 1]
                travel_time = travel_times[meeting["location"]][next_meeting["location"]]
                
                itinerary.append({
                    "action": "travel",
                    "location": next_meeting["location"],
                    "person": "",
                    "start_time": minutes_to_time(meeting["end"]),
                    "end_time": minutes_to_time(meeting["end"] + travel_time)
                })
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()