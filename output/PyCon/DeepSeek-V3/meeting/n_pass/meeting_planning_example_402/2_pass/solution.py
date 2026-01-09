from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = ["Golden Gate Park", "Haight-Ashbury", "Sunset District", "Marina District", "Financial District", "Union Square"]
    
    # Travel times matrix (in minutes)
    travel_times = {
        "Golden Gate Park": {"Golden Gate Park": 0, "Haight-Ashbury": 7, "Sunset District": 10, "Marina District": 16, "Financial District": 26, "Union Square": 22},
        "Haight-Ashbury": {"Golden Gate Park": 7, "Haight-Ashbury": 0, "Sunset District": 15, "Marina District": 17, "Financial District": 21, "Union Square": 17},
        "Sunset District": {"Golden Gate Park": 11, "Haight-Ashbury": 15, "Sunset District": 0, "Marina District": 21, "Financial District": 30, "Union Square": 30},
        "Marina District": {"Golden Gate Park": 18, "Haight-Ashbury": 16, "Sunset District": 19, "Marina District": 0, "Financial District": 17, "Union Square": 16},
        "Financial District": {"Golden Gate Park": 23, "Haight-Ashbury": 19, "Sunset District": 31, "Marina District": 15, "Financial District": 0, "Union Square": 9},
        "Union Square": {"Golden Gate Park": 22, "Haight-Ashbury": 18, "Sunset District": 26, "Marina District": 18, "Financial District": 9, "Union Square": 0}
    }
    
    # Friend constraints
    friends = {
        "Sarah": {
            "location": "Haight-Ashbury",
            "available_start": datetime.strptime("17:00", "%H:%M"),
            "available_end": datetime.strptime("21:30", "%H:%M"),
            "min_duration": 105
        },
        "Patricia": {
            "location": "Sunset District",
            "available_start": datetime.strptime("17:00", "%H:%M"),
            "available_end": datetime.strptime("19:45", "%H:%M"),
            "min_duration": 45
        },
        "Matthew": {
            "location": "Marina District",
            "available_start": datetime.strptime("9:15", "%H:%M"),
            "available_end": datetime.strptime("12:00", "%H:%M"),
            "min_duration": 15
        },
        "Joseph": {
            "location": "Financial District",
            "available_start": datetime.strptime("14:15", "%H:%M"),
            "available_end": datetime.strptime("18:45", "%H:%M"),
            "min_duration": 30
        },
        "Robert": {
            "location": "Union Square",
            "available_start": datetime.strptime("10:15", "%H:%M"),
            "available_end": datetime.strptime("21:45", "%H:%M"),
            "min_duration": 15
        }
    }
    
    # Start at Golden Gate Park at 9:00 AM
    current_time = datetime.strptime("9:00", "%H:%M")
    current_location = "Golden Gate Park"
    
    def find_best_schedule():
        best_schedule = []
        best_total_duration = 0
        
        # Try all permutations of friends
        from itertools import permutations
        
        # Since there are 5 friends, 5! = 120 permutations is manageable
        for order in permutations(friends.keys()):
            schedule = []
            current_loc = current_location
            current_time_local = current_time
            total_duration = 0
            
            for friend_name in order:
                friend = friends[friend_name]
                
                # Calculate earliest possible start time at friend's location
                travel_time = travel_times[current_loc][friend["location"]]
                arrival_time = current_time_local + timedelta(minutes=travel_time)
                
                # Start time is the later of arrival time and friend's available start
                start_time = max(arrival_time, friend["available_start"])
                
                # Check if we can meet within friend's availability
                if start_time + timedelta(minutes=friend["min_duration"]) <= friend["available_end"]:
                    # Use minimum duration for simplicity
                    end_time = start_time + timedelta(minutes=friend["min_duration"])
                    
                    schedule.append({
                        "friend": friend_name,
                        "location": friend["location"],
                        "start": start_time,
                        "end": end_time
                    })
                    
                    total_duration += friend["min_duration"]
                    current_loc = friend["location"]
                    current_time_local = end_time
                else:
                    # Can't meet this friend in this order
                    break
            
            if total_duration > best_total_duration:
                best_total_duration = total_duration
                best_schedule = schedule
        
        return best_schedule
    
    # Find the best schedule
    best_schedule = find_best_schedule()
    
    # Build itinerary
    itinerary = []
    
    if best_schedule:
        # Add travel from starting location to first meeting
        first_meeting = best_schedule[0]
        travel_start = current_time
        travel_end = current_time + timedelta(minutes=travel_times[current_location][first_meeting["location"]])
        
        itinerary.append({
            "action": "travel",
            "location": first_meeting["location"],
            "person": "",
            "start_time": travel_start.strftime("%H:%M"),
            "end_time": travel_end.strftime("%H:%M")
        })
        
        # Add meetings and travel between them
        for i, meeting in enumerate(best_schedule):
            # Add the meeting
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["friend"],
                "start_time": meeting["start"].strftime("%H:%M"),
                "end_time": meeting["end"].strftime("%H:%M")
            })
            
            # Add travel to next meeting if there is one
            if i < len(best_schedule) - 1:
                next_meeting = best_schedule[i + 1]
                travel_time_needed = travel_times[meeting["location"]][next_meeting["location"]]
                
                travel_start = meeting["end"]
                travel_end = travel_start + timedelta(minutes=travel_time_needed)
                
                itinerary.append({
                    "action": "travel",
                    "location": next_meeting["location"],
                    "person": "",
                    "start_time": travel_start.strftime("%H:%M"),
                    "end_time": travel_end.strftime("%H:%M")
                })
    
    # Output as JSON
    output = {
        "itinerary": itinerary
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()