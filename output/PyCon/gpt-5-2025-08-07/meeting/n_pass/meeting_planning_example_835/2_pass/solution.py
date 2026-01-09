import json
from datetime import datetime, timedelta

def main():
    # Define locations
    locations = [
        "Pacific Heights", "Golden Gate Park", "The Castro", "Bayview", 
        "Marina District", "Union Square", "Sunset District", "Alamo Square", 
        "Financial District", "Mission District"
    ]
    
    # Travel times matrix (minutes)
    travel_times = {
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Mission District"): 15,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Mission District"): 17,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Mission District"): 7,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Mission District"): 13,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Mission District"): 20,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Mission District"): 14,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Mission District"): 25,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Mission District"): 10,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Mission District"): 17,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Financial District"): 15
    }
    
    # Friend constraints
    friends = [
        {"name": "Helen", "location": "Golden Gate Park", "start": "9:30", "end": "12:15", "min_duration": 45},
        {"name": "Steven", "location": "The Castro", "start": "20:15", "end": "22:00", "min_duration": 105},
        {"name": "Deborah", "location": "Bayview", "start": "8:30", "end": "12:00", "min_duration": 30},
        {"name": "Matthew", "location": "Marina District", "start": "9:15", "end": "14:15", "min_duration": 45},
        {"name": "Joseph", "location": "Union Square", "start": "14:15", "end": "18:45", "min_duration": 120},
        {"name": "Ronald", "location": "Sunset District", "start": "16:00", "end": "20:45", "min_duration": 60},
        {"name": "Robert", "location": "Alamo Square", "start": "18:30", "end": "21:15", "min_duration": 120},
        {"name": "Rebecca", "location": "Financial District", "start": "14:45", "end": "16:15", "min_duration": 30},
        {"name": "Elizabeth", "location": "Mission District", "start": "18:30", "end": "21:00", "min_duration": 120}
    ]
    
    # Convert time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Preprocess friend data
    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["start"])
        friend["end_min"] = time_to_minutes(friend["end"])
    
    # Start from Pacific Heights at 9:00
    current_time = time_to_minutes("9:00")
    current_location = "Pacific Heights"
    itinerary = []
    scheduled_meetings = []
    
    # Sort friends by their start time for a greedy approach
    available_friends = friends.copy()
    
    while available_friends and current_time < time_to_minutes("22:00"):
        # Find the next feasible meeting
        best_friend = None
        best_start_time = None
        best_end_time = None
        
        for friend in available_friends:
            # Calculate earliest possible start time considering travel
            travel_time = travel_times.get((current_location, friend["location"]), 60)
            earliest_start = current_time + travel_time
            
            # Check if we can meet this friend
            if earliest_start <= friend["end_min"] - friend["min_duration"]:
                # Start as early as possible within friend's availability
                start_time = max(earliest_start, friend["start_min"])
                end_time = start_time + friend["min_duration"]
                
                # Check if this fits within friend's time window
                if end_time <= friend["end_min"]:
                    if best_friend is None or start_time < best_start_time:
                        best_friend = friend
                        best_start_time = start_time
                        best_end_time = end_time
        
        if best_friend is None:
            # No more feasible meetings
            break
        
        # Add travel if needed
        if current_location != best_friend["location"]:
            travel_time = travel_times.get((current_location, best_friend["location"]), 60)
            travel_start = current_time
            travel_end = current_time + travel_time
            
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": best_friend["location"],
                "start_time": minutes_to_time(travel_start),
                "end_time": minutes_to_time(travel_end)
            })
            
            current_time = travel_end
            current_location = best_friend["location"]
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": best_friend["location"],
            "person": best_friend["name"],
            "start_time": minutes_to_time(best_start_time),
            "end_time": minutes_to_time(best_end_time)
        })
        
        scheduled_meetings.append(best_friend)
        current_time = best_end_time
        
        # Remove scheduled friend from available list
        available_friends.remove(best_friend)
    
    # If we couldn't schedule all friends, try to fit in remaining ones
    # by checking if we have time gaps where we can insert them
    if available_friends:
        # Create a timeline of scheduled activities
        timeline = []
        for item in itinerary:
            start_min = time_to_minutes(item["start_time"])
            end_min = time_to_minutes(item["end_time"])
            timeline.append((start_min, end_min, item))
        
        # Sort timeline by start time
        timeline.sort(key=lambda x: x[0])
        
        # Try to insert remaining friends in gaps
        for friend in available_friends.copy():
            for i in range(len(timeline) - 1):
                gap_start = timeline[i][1]  # end of current activity
                gap_end = timeline[i + 1][0]  # start of next activity
                
                if gap_end - gap_start >= friend["min_duration"]:
                    # Check if we can travel to friend's location and back
                    current_loc_at_gap = timeline[i][2].get("to", timeline[i][2].get("location", "Pacific Heights"))
                    
                    travel_to = travel_times.get((current_loc_at_gap, friend["location"]), 60)
                    travel_back = travel_times.get((friend["location"], timeline[i + 1][2].get("from", timeline[i + 1][2].get("location", "Pacific Heights"))), 60)
                    
                    total_travel = travel_to + travel_back
                    available_time = gap_end - gap_start
                    
                    if available_time >= friend["min_duration"] + total_travel:
                        # We can fit this meeting in the gap
                        meeting_start = gap_start + travel_to
                        meeting_end = meeting_start + friend["min_duration"]
                        
                        # Check if it fits in friend's time window
                        if (meeting_start >= friend["start_min"] and 
                            meeting_end <= friend["end_min"] and
                            meeting_end + travel_back <= gap_end):
                            
                            # Insert travel and meeting into itinerary
                            new_items = [
                                {
                                    "action": "travel",
                                    "from": current_loc_at_gap,
                                    "to": friend["location"],
                                    "start_time": minutes_to_time(gap_start),
                                    "end_time": minutes_to_time(gap_start + travel_to)
                                },
                                {
                                    "action": "meet",
                                    "location": friend["location"],
                                    "person": friend["name"],
                                    "start_time": minutes_to_time(meeting_start),
                                    "end_time": minutes_to_time(meeting_end)
                                },
                                {
                                    "action": "travel",
                                    "from": friend["location"],
                                    "to": timeline[i + 1][2].get("from", timeline[i + 1][2].get("location", "Pacific Heights")),
                                    "start_time": minutes_to_time(meeting_end),
                                    "end_time": minutes_to_time(meeting_end + travel_back)
                                }
                            ]
                            
                            # Find insertion point in itinerary
                            insert_index = 0
                            for idx, item in enumerate(itinerary):
                                if time_to_minutes(item["start_time"]) >= gap_start:
                                    insert_index = idx
                                    break
                            
                            # Insert new items
                            itinerary[insert_index:insert_index] = new_items
                            scheduled_meetings.append(friend)
                            available_friends.remove(friend)
                            break
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()