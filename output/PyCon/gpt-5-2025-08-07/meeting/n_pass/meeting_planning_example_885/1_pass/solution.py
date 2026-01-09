import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define all locations
    locations = [
        "Russian Hill", "Marina District", "Financial District", "Alamo Square",
        "Golden Gate Park", "The Castro", "Bayview", "Sunset District",
        "Haight-Ashbury", "Nob Hill"
    ]
    
    # Travel times matrix (minutes)
    travel_times = {
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Nob Hill"): 5,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Nob Hill"): 8,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Nob Hill"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Nob Hill"): 16,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Nob Hill"): 27,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Haight-Ashbury"): 13,
    }
    
    # Friend constraints
    friends = {
        "Mark": {
            "location": "Marina District",
            "available_start": datetime.strptime("18:45", "%H:%M"),
            "available_end": datetime.strptime("21:00", "%H:%M"),
            "min_duration": 90  # minutes
        },
        "Karen": {
            "location": "Financial District",
            "available_start": datetime.strptime("9:30", "%H:%M"),
            "available_end": datetime.strptime("12:45", "%H:%M"),
            "min_duration": 90
        },
        "Barbara": {
            "location": "Alamo Square",
            "available_start": datetime.strptime("10:00", "%H:%M"),
            "available_end": datetime.strptime("19:30", "%H:%M"),
            "min_duration": 90
        },
        "Nancy": {
            "location": "Golden Gate Park",
            "available_start": datetime.strptime("16:45", "%H:%M"),
            "available_end": datetime.strptime("20:00", "%H:%M"),
            "min_duration": 105
        },
        "David": {
            "location": "The Castro",
            "available_start": datetime.strptime("9:00", "%H:%M"),
            "available_end": datetime.strptime("18:00", "%H:%M"),
            "min_duration": 120
        },
        "Linda": {
            "location": "Bayview",
            "available_start": datetime.strptime("18:15", "%H:%M"),
            "available_end": datetime.strptime("19:45", "%H:%M"),
            "min_duration": 45
        },
        "Kevin": {
            "location": "Sunset District",
            "available_start": datetime.strptime("10:00", "%H:%M"),
            "available_end": datetime.strptime("17:45", "%H:%M"),
            "min_duration": 120
        },
        "Matthew": {
            "location": "Haight-Ashbury",
            "available_start": datetime.strptime("10:15", "%H:%M"),
            "available_end": datetime.strptime("15:30", "%H:%M"),
            "min_duration": 45
        },
        "Andrew": {
            "location": "Nob Hill",
            "available_start": datetime.strptime("11:45", "%H:%M"),
            "available_end": datetime.strptime("16:45", "%H:%M"),
            "min_duration": 105
        }
    }
    
    # Start at Russian Hill at 9:00
    current_time = datetime.strptime("9:00", "%H:%M")
    current_location = "Russian Hill"
    
    # Create problem
    problem = constraint.Problem()
    
    # We'll try to maximize number of friends met by trying different orders
    # For simplicity, we'll use a greedy approach with backtracking
    
    def time_to_minutes(time_str):
        """Convert time string to minutes since midnight"""
        dt = datetime.strptime(time_str, "%H:%M")
        return dt.hour * 60 + dt.minute
    
    def minutes_to_time(minutes):
        """Convert minutes since midnight to time string"""
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Convert all times to minutes for easier calculation
    friends_minutes = {}
    for name, info in friends.items():
        friends_minutes[name] = {
            "location": info["location"],
            "available_start": time_to_minutes(info["available_start"].strftime("%H:%M")),
            "available_end": time_to_minutes(info["available_end"].strftime("%H:%M")),
            "min_duration": info["min_duration"]
        }
    
    # Start optimization
    best_schedule = []
    max_friends = 0
    
    # Try different permutations of friends
    from itertools import permutations
    
    friend_names = list(friends.keys())
    
    # Limit to reasonable permutations to avoid combinatorial explosion
    for perm in permutations(friend_names, min(6, len(friend_names))):
        schedule = []
        current_loc = "Russian Hill"
        current_minutes = time_to_minutes("9:00")
        day_end = time_to_minutes("21:00")  # End of day
        
        for friend in perm:
            info = friends_minutes[friend]
            loc = info["location"]
            
            # Calculate travel time
            travel_time = travel_times.get((current_loc, loc), 30)  # Default to 30 if not found
            
            # Arrival time at friend's location
            arrival_time = current_minutes + travel_time
            
            # Check if we can meet this friend
            if arrival_time >= info["available_start"] and arrival_time < info["available_end"]:
                # Calculate meeting end time
                meeting_end = min(arrival_time + info["min_duration"], info["available_end"], day_end)
                
                # Check if meeting is valid
                if meeting_end - arrival_time >= info["min_duration"]:
                    schedule.append({
                        "friend": friend,
                        "location": loc,
                        "start_time": minutes_to_time(arrival_time),
                        "end_time": minutes_to_time(meeting_end)
                    })
                    current_loc = loc
                    current_minutes = meeting_end
        
        # Update best schedule if this one is better
        if len(schedule) > max_friends:
            max_friends = len(schedule)
            best_schedule = schedule
    
    # If no valid schedule found with permutations, try a greedy approach
    if not best_schedule:
        current_loc = "Russian Hill"
        current_minutes = time_to_minutes("9:00")
        day_end = time_to_minutes("21:00")
        
        remaining_friends = list(friend_names)
        
        while remaining_friends and current_minutes < day_end:
            best_next_friend = None
            best_meeting_end = day_end + 1
            
            for friend in remaining_friends:
                info = friends_minutes[friend]
                loc = info["location"]
                
                travel_time = travel_times.get((current_loc, loc), 30)
                arrival_time = current_minutes + travel_time
                
                if arrival_time >= info["available_start"] and arrival_time < info["available_end"]:
                    meeting_end = min(arrival_time + info["min_duration"], info["available_end"], day_end)
                    
                    if meeting_end - arrival_time >= info["min_duration"] and meeting_end < best_meeting_end:
                        best_next_friend = friend
                        best_meeting_end = meeting_end
            
            if best_next_friend:
                info = friends_minutes[best_next_friend]
                loc = info["location"]
                travel_time = travel_times.get((current_loc, loc), 30)
                arrival_time = current_minutes + travel_time
                meeting_end = best_meeting_end
                
                best_schedule.append({
                    "friend": best_next_friend,
                    "location": loc,
                    "start_time": minutes_to_time(arrival_time),
                    "end_time": minutes_to_time(meeting_end)
                })
                
                current_loc = loc
                current_minutes = meeting_end
                remaining_friends.remove(best_next_friend)
            else:
                break
    
    # Format output
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["friend"],
            "start_time": meeting["start_time"],
            "end_time": meeting["end_time"]
        })
    
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()