from datetime import datetime, timedelta
import json

def main():
    # Define all locations
    locations = [
        "Sunset District", "Presidio", "Nob Hill", "Pacific Heights", "Mission District",
        "Marina District", "North Beach", "Russian Hill", "Richmond District", 
        "Embarcadero", "Alamo Square"
    ]
    
    # Travel times dictionary (in minutes)
    travel_times = {
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Alamo Square"): 15,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Alamo Square"): 15,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Alamo Square"): 13,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Alamo Square"): 19,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16
    }
    
    # Friend constraints
    friends = [
        {"name": "Charles", "location": "Presidio", "available_start": "13:15", "available_end": "15:00", "min_duration": 105},
        {"name": "Robert", "location": "Nob Hill", "available_start": "13:15", "available_end": "17:30", "min_duration": 90},
        {"name": "Nancy", "location": "Pacific Heights", "available_start": "14:45", "available_end": "22:00", "min_duration": 105},
        {"name": "Brian", "location": "Mission District", "available_start": "15:30", "available_end": "22:00", "min_duration": 60},
        {"name": "Kimberly", "location": "Marina District", "available_start": "17:00", "available_end": "19:45", "min_duration": 75},
        {"name": "David", "location": "North Beach", "available_start": "14:45", "available_end": "16:30", "min_duration": 75},
        {"name": "William", "location": "Russian Hill", "available_start": "12:30", "available_end": "19:15", "min_duration": 120},
        {"name": "Jeffrey", "location": "Richmond District", "available_start": "12:00", "available_end": "19:15", "min_duration": 45},
        {"name": "Karen", "location": "Embarcadero", "available_start": "14:15", "available_end": "20:45", "min_duration": 60},
        {"name": "Joshua", "location": "Alamo Square", "available_start": "18:45", "available_end": "22:00", "min_duration": 60}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
        else:
            hours = int(time_str)
            minutes = 0
        return (hours - 9) * 60 + minutes
    
    # Convert minutes since 9:00 to time string
    def minutes_to_time(minutes):
        total_hours = 9 + minutes // 60
        total_minutes = minutes % 60
        return f"{total_hours}:{total_minutes:02d}"
    
    # Get travel time between two locations
    def get_travel_time(from_loc, to_loc):
        return travel_times.get((from_loc, to_loc), 30)
    
    # Find optimal schedule using backtracking
    def find_optimal_schedule(current_time, current_location, remaining_friends, current_schedule):
        if not remaining_friends:
            return current_schedule.copy()
        
        best_schedule = None
        best_total_time = 0
        
        for i, friend in enumerate(remaining_friends):
            # Calculate travel time
            travel_time = get_travel_time(current_location, friend["location"])
            
            # Calculate earliest possible start time
            earliest_start = max(current_time + travel_time, time_to_minutes(friend["available_start"]))
            latest_start = time_to_minutes(friend["available_end"]) - friend["min_duration"]
            
            # If we can meet this friend
            if earliest_start <= latest_start:
                # Try meeting for minimum duration
                meeting_start = earliest_start
                meeting_end = meeting_start + friend["min_duration"]
                
                # Create new schedule entry
                new_entry = {
                    "friend": friend,
                    "start": meeting_start,
                    "end": meeting_end,
                    "location": friend["location"]
                }
                
                # Update remaining friends and schedule
                new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                new_schedule = current_schedule + [new_entry]
                
                # Recursively find schedule for remaining friends
                result_schedule = find_optimal_schedule(meeting_end, friend["location"], new_remaining, new_schedule)
                
                if result_schedule:
                    # Calculate total meeting time
                    total_time = sum(entry["end"] - entry["start"] for entry in result_schedule)
                    if total_time > best_total_time:
                        best_total_time = total_time
                        best_schedule = result_schedule
        
        return best_schedule
    
    # Start from Sunset District at 9:00
    start_time = time_to_minutes("9:00")
    start_location = "Sunset District"
    
    # Find optimal schedule
    optimal_schedule = find_optimal_schedule(start_time, start_location, friends, [])
    
    # If no optimal schedule found, try a greedy approach
    if not optimal_schedule:
        optimal_schedule = []
        current_time = start_time
        current_location = start_location
        remaining_friends = friends.copy()
        
        while remaining_friends:
            best_friend = None
            best_start_time = float('inf')
            best_travel_time = float('inf')
            
            for friend in remaining_friends:
                travel_time = get_travel_time(current_location, friend["location"])
                earliest_start = max(current_time + travel_time, time_to_minutes(friend["available_start"]))
                latest_start = time_to_minutes(friend["available_end"]) - friend["min_duration"]
                
                if earliest_start <= latest_start and earliest_start < best_start_time:
                    best_friend = friend
                    best_start_time = earliest_start
                    best_travel_time = travel_time
            
            if best_friend:
                meeting_start = best_start_time
                meeting_end = meeting_start + best_friend["min_duration"]
                
                optimal_schedule.append({
                    "friend": best_friend,
                    "start": meeting_start,
                    "end": meeting_end,
                    "location": best_friend["location"]
                })
                
                current_time = meeting_end
                current_location = best_friend["location"]
                remaining_friends.remove(best_friend)
            else:
                break
    
    # Sort schedule by start time
    optimal_schedule.sort(key=lambda x: x["start"])
    
    # Build itinerary
    itinerary = []
    current_time = start_time
    current_location = start_location
    
    for meeting in optimal_schedule:
        # Add travel if needed
        travel_time = get_travel_time(current_location, meeting["location"])
        if travel_time > 0 and current_time + travel_time <= meeting["start"]:
            itinerary.append({
                "action": "travel",
                "location": meeting["location"],
                "person": "",
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(current_time + travel_time)
            })
            current_time += travel_time
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["friend"]["name"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        })
        
        current_time = meeting["end"]
        current_location = meeting["location"]
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()