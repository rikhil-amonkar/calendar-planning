import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric)
    travel_times = {
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Presidio"): 16,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Presidio"): 24,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Presidio"): 10,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Presidio"): 7,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Presidio"): 20,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Presidio"): 20,
        ("Alamo Square", "Presidio"): 17,
    }
    
    # Make travel times symmetric
    symmetric_travel = travel_times.copy()
    for (loc1, loc2), time in travel_times.items():
        symmetric_travel[(loc2, loc1)] = time
    
    # Friend constraints
    friends = [
        {"name": "David", "location": "Sunset District", "start": "9:15", "end": "22:00", "min_duration": 15},
        {"name": "Kenneth", "location": "Union Square", "start": "21:15", "end": "21:45", "min_duration": 15},
        {"name": "Patricia", "location": "Nob Hill", "start": "15:00", "end": "19:15", "min_duration": 120},
        {"name": "Mary", "location": "Marina District", "start": "14:45", "end": "16:45", "min_duration": 45},
        {"name": "Charles", "location": "Richmond District", "start": "17:15", "end": "21:00", "min_duration": 15},
        {"name": "Joshua", "location": "Financial District", "start": "14:30", "end": "17:15", "min_duration": 90},
        {"name": "Ronald", "location": "Embarcadero", "start": "18:15", "end": "20:45", "min_duration": 30},
        {"name": "George", "location": "The Castro", "start": "14:15", "end": "19:00", "min_duration": 105},
        {"name": "Kimberly", "location": "Alamo Square", "start": "9:00", "end": "14:30", "min_duration": 105},
        {"name": "William", "location": "Presidio", "start": "7:00", "end": "12:45", "min_duration": 60}
    ]
    
    # Convert all times to minutes
    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["start"])
        friend["end_min"] = time_to_minutes(friend["end"])
    
    # Start at Russian Hill at 9:00 AM
    current_time = time_to_minutes("9:00")
    current_location = "Russian Hill"
    
    itinerary = []
    remaining_friends = friends.copy()
    
    # Simple greedy algorithm to schedule meetings
    while remaining_friends and current_time < time_to_minutes("23:00"):
        best_friend = None
        best_score = -1
        
        for friend in remaining_friends:
            # Calculate travel time
            travel_time = symmetric_travel.get((current_location, friend["location"]), 30)
            
            # Calculate earliest possible start time
            earliest_start = current_time + travel_time
            latest_start = friend["end_min"] - friend["min_duration"]
            
            # Check if meeting is possible
            if earliest_start <= latest_start and earliest_start >= friend["start_min"]:
                # Calculate actual meeting time (start as early as possible)
                meeting_start = max(earliest_start, friend["start_min"])
                meeting_end = meeting_start + friend["min_duration"]
                
                if meeting_end <= friend["end_min"]:
                    # Score based on time efficiency and duration
                    score = friend["min_duration"] - travel_time
                    
                    if score > best_score:
                        best_score = score
                        best_friend = friend
                        best_meeting_start = meeting_start
                        best_meeting_end = meeting_end
        
        if best_friend:
            # Add meeting to itinerary
            itinerary.append({
                "action": "meet",
                "location": best_friend["location"],
                "person": best_friend["name"],
                "start_time": minutes_to_time(best_meeting_start),
                "end_time": minutes_to_time(best_meeting_end)
            })
            
            # Update current state
            current_time = best_meeting_end
            current_location = best_friend["location"]
            remaining_friends.remove(best_friend)
        else:
            # No feasible meetings found, break
            break
    
    # Output result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()