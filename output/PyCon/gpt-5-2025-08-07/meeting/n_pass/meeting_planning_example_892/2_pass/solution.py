import json
from datetime import datetime, timedelta

def main():
    # Define locations
    locations = [
        "Marina District", "Bayview", "Sunset District", "Richmond District", 
        "Nob Hill", "Chinatown", "Haight-Ashbury", "North Beach", 
        "Russian Hill", "Embarcadero"
    ]
    
    # Create travel time matrix
    travel_times = {
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Embarcadero"): 14,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Embarcadero"): 19,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Embarcadero"): 30,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Embarcadero"): 19,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Embarcadero"): 9,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Embarcadero"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Bayview"): 25,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Embarcadero"): 6,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Embarcadero"): 8,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Russian Hill"): 8
    }
    
    # Define friend constraints
    friends = [
        {"name": "Charles", "location": "Bayview", "start": "11:30", "end": "14:30", "min_duration": 45},
        {"name": "Robert", "location": "Sunset District", "start": "16:45", "end": "21:00", "min_duration": 30},
        {"name": "Karen", "location": "Richmond District", "start": "19:15", "end": "21:30", "min_duration": 60},
        {"name": "Rebecca", "location": "Nob Hill", "start": "16:15", "end": "20:30", "min_duration": 90},
        {"name": "Margaret", "location": "Chinatown", "start": "14:15", "end": "19:45", "min_duration": 120},
        {"name": "Patricia", "location": "Haight-Ashbury", "start": "14:30", "end": "20:30", "min_duration": 45},
        {"name": "Mark", "location": "North Beach", "start": "14:00", "end": "18:30", "min_duration": 105},
        {"name": "Melissa", "location": "Russian Hill", "start": "13:00", "end": "19:45", "min_duration": 30},
        {"name": "Laura", "location": "Embarcadero", "start": "7:45", "end": "13:15", "min_duration": 105}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, "%H:%M")
        base_time = datetime.strptime("9:00", "%H:%M")
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)
    
    # Convert minutes since 9:00 to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime("9:00", "%H:%M")
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime("%H:%M").lstrip("0")
    
    # Precompute time windows for each friend
    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["start"])
        friend["end_min"] = time_to_minutes(friend["end"])
    
    # Start from Marina District at 9:00
    current_time = 0  # 9:00 in minutes since 9:00
    current_location = "Marina District"
    
    # Sort friends by their availability windows to prioritize those with tighter constraints
    friends_sorted = sorted(friends, key=lambda x: (x["start_min"], x["end_min"]))
    
    itinerary = []
    scheduled = [False] * len(friends_sorted)
    
    def schedule_meeting(current_time, current_location, depth=0):
        if depth == len(friends_sorted):
            return True
        
        for i, friend in enumerate(friends_sorted):
            if scheduled[i]:
                continue
            
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend["location"]), 60)
            
            # Earliest we can start this meeting
            earliest_start = max(current_time + travel_time, friend["start_min"])
            
            # Check if we can schedule this meeting
            if earliest_start + friend["min_duration"] <= friend["end_min"]:
                # Try to schedule this meeting
                scheduled[i] = True
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(earliest_start),
                    "end_time": minutes_to_time(earliest_start + friend["min_duration"])
                })
                
                # Recursively schedule remaining meetings
                if schedule_meeting(earliest_start + friend["min_duration"], friend["location"], depth + 1):
                    return True
                
                # Backtrack if this path didn't work
                scheduled[i] = False
                itinerary.pop()
        
        return False
    
    # Try to schedule all meetings
    success = schedule_meeting(current_time, current_location)
    
    if not success:
        # Fallback: greedy scheduling without backtracking
        itinerary = []
        current_time = 0
        current_location = "Marina District"
        scheduled = [False] * len(friends)
        
        # Sort by end time for greedy approach
        friends_sorted_greedy = sorted(friends, key=lambda x: x["end_min"])
        
        for friend in friends_sorted_greedy:
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend["location"]), 60)
            
            # Earliest we can start this meeting
            earliest_start = max(current_time + travel_time, friend["start_min"])
            
            # Check if we can schedule this meeting
            if earliest_start + friend["min_duration"] <= friend["end_min"]:
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(earliest_start),
                    "end_time": minutes_to_time(earliest_start + friend["min_duration"])
                })
                current_time = earliest_start + friend["min_duration"]
                current_location = friend["location"]
                scheduled[friends.index(friend)] = True
        
        # Try to schedule any remaining friends
        remaining_friends = [f for i, f in enumerate(friends) if not scheduled[i]]
        for friend in remaining_friends:
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend["location"]), 60)
            
            # Earliest we can start this meeting
            earliest_start = max(current_time + travel_time, friend["start_min"])
            
            # Check if we can schedule this meeting (even if it means extending beyond original constraints)
            if earliest_start <= friend["end_min"]:
                duration = min(friend["min_duration"], friend["end_min"] - earliest_start)
                if duration > 0:
                    itinerary.append({
                        "action": "meet",
                        "location": friend["location"],
                        "person": friend["name"],
                        "start_time": minutes_to_time(earliest_start),
                        "end_time": minutes_to_time(earliest_start + duration)
                    })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()