import json
from datetime import datetime, timedelta

def main():
    # Define locations and travel times
    locations = [
        "Union Square", "The Castro", "North Beach", "Embarcadero", 
        "Alamo Square", "Nob Hill", "Presidio", "Fisherman's Wharf", 
        "Mission District", "Haight-Ashbury"
    ]
    
    # Travel times matrix (in minutes)
    travel_times = {
        ("Union Square", "The Castro"): 17,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Haight-Ashbury"): 18,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Haight-Ashbury"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Haight-Ashbury"): 18,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Mission District"): 11,
    }
    
    # Friend constraints
    friends = [
        {"name": "Melissa", "location": "The Castro", "start": "20:15", "end": "21:15", "min_duration": 30},
        {"name": "Kimberly", "location": "North Beach", "start": "7:00", "end": "10:30", "min_duration": 15},
        {"name": "Joseph", "location": "Embarcadero", "start": "15:30", "end": "19:30", "min_duration": 75},
        {"name": "Barbara", "location": "Alamo Square", "start": "20:45", "end": "21:45", "min_duration": 15},
        {"name": "Kenneth", "location": "Nob Hill", "start": "12:15", "end": "17:15", "min_duration": 105},
        {"name": "Joshua", "location": "Presidio", "start": "16:30", "end": "18:15", "min_duration": 105},
        {"name": "Brian", "location": "Fisherman's Wharf", "start": "9:30", "end": "15:30", "min_duration": 45},
        {"name": "Steven", "location": "Mission District", "start": "19:30", "end": "21:00", "min_duration": 90},
        {"name": "Betty", "location": "Haight-Ashbury", "start": "19:00", "end": "20:30", "min_duration": 90}
    ]
    
    # Convert time strings to minutes since 0:00 for easier calculations
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Pre-calculate time windows for each friend
    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["start"])
        friend["end_min"] = time_to_minutes(friend["end"])
    
    # Start from Union Square at 9:00
    start_location = "Union Square"
    start_time = time_to_minutes("9:00")
    
    def find_best_itinerary(current_time, current_location, remaining_friends, current_itinerary):
        if not remaining_friends:
            return current_itinerary[:]
        
        best_itinerary = None
        
        for i, friend in enumerate(remaining_friends):
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend["location"]), 30)
            
            # Earliest possible start time considering travel
            earliest_start = max(current_time + travel_time, friend["start_min"])
            
            # Check if meeting is possible
            if earliest_start + friend["min_duration"] <= friend["end_min"]:
                # Schedule this meeting
                new_itinerary_item = {
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(earliest_start),
                    "end_time": minutes_to_time(earliest_start + friend["min_duration"])
                }
                
                # Create new state
                new_time = earliest_start + friend["min_duration"]
                new_location = friend["location"]
                new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                new_itinerary = current_itinerary + [new_itinerary_item]
                
                # Recursively try to schedule remaining friends
                result = find_best_itinerary(new_time, new_location, new_remaining, new_itinerary)
                
                # Keep the best result (the one that schedules the most friends)
                if result is not None:
                    if best_itinerary is None or len(result) > len(best_itinerary):
                        best_itinerary = result
        
        return best_itinerary
    
    # Try different orderings to find the best schedule
    def optimize_schedule():
        # Sort friends by various criteria and try different orderings
        orderings = [
            sorted(friends, key=lambda x: x["start_min"]),  # Earliest start time
            sorted(friends, key=lambda x: x["end_min"]),    # Earliest end time
            sorted(friends, key=lambda x: x["min_duration"]),  # Shortest duration
            sorted(friends, key=lambda x: -x["min_duration"]),  # Longest duration
        ]
        
        best_result = None
        
        for ordering in orderings:
            result = find_best_itinerary(start_time, start_location, ordering, [])
            if result is not None:
                if best_result is None or len(result) > len(best_result):
                    best_result = result
        
        # If no complete schedule found, use greedy approach
        if best_result is None:
            best_result = greedy_schedule()
        
        return best_result
    
    def greedy_schedule():
        # Simple greedy scheduling as fallback
        itinerary = []
        current_time = start_time
        current_location = start_location
        
        # Sort by end time
        sorted_friends = sorted(friends, key=lambda x: x["end_min"])
        
        for friend in sorted_friends:
            travel_time = travel_times.get((current_location, friend["location"]), 30)
            earliest_start = max(current_time + travel_time, friend["start_min"])
            
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
        
        return itinerary
    
    # Find the best itinerary
    itinerary = optimize_schedule()
    
    if not itinerary:
        itinerary = []  # Empty itinerary as last resort
    
    result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()