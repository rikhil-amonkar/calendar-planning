import json
from datetime import datetime, timedelta

def main():
    # Define all locations
    locations = [
        "Union Square", "Presidio", "Alamo Square", "Marina District", 
        "Financial District", "Nob Hill", "Sunset District", "Chinatown", 
        "Russian Hill", "North Beach", "Haight-Ashbury"
    ]
    
    # Create travel time matrix
    travel_times = {}
    for loc in locations:
        travel_times[loc] = {}
    
    # Union Square travel times
    travel_times["Union Square"]["Presidio"] = 24
    travel_times["Union Square"]["Alamo Square"] = 15
    travel_times["Union Square"]["Marina District"] = 18
    travel_times["Union Square"]["Financial District"] = 9
    travel_times["Union Square"]["Nob Hill"] = 9
    travel_times["Union Square"]["Sunset District"] = 27
    travel_times["Union Square"]["Chinatown"] = 7
    travel_times["Union Square"]["Russian Hill"] = 13
    travel_times["Union Square"]["North Beach"] = 10
    travel_times["Union Square"]["Haight-Ashbury"] = 18
    
    # Presidio travel times
    travel_times["Presidio"]["Union Square"] = 22
    travel_times["Presidio"]["Alamo Square"] = 19
    travel_times["Presidio"]["Marina District"] = 11
    travel_times["Presidio"]["Financial District"] = 23
    travel_times["Presidio"]["Nob Hill"] = 18
    travel_times["Presidio"]["Sunset District"] = 15
    travel_times["Presidio"]["Chinatown"] = 21
    travel_times["Presidio"]["Russian Hill"] = 14
    travel_times["Presidio"]["North Beach"] = 18
    travel_times["Presidio"]["Haight-Ashbury"] = 15
    
    # Alamo Square travel times
    travel_times["Alamo Square"]["Union Square"] = 14
    travel_times["Alamo Square"]["Presidio"] = 17
    travel_times["Alamo Square"]["Marina District"] = 15
    travel_times["Alamo Square"]["Financial District"] = 17
    travel_times["Alamo Square"]["Nob Hill"] = 11
    travel_times["Alamo Square"]["Sunset District"] = 16
    travel_times["Alamo Square"]["Chinatown"] = 15
    travel_times["Alamo Square"]["Russian Hill"] = 13
    travel_times["Alamo Square"]["North Beach"] = 15
    travel_times["Alamo Square"]["Haight-Ashbury"] = 5
    
    # Marina District travel times
    travel_times["Marina District"]["Union Square"] = 16
    travel_times["Marina District"]["Presidio"] = 10
    travel_times["Marina District"]["Alamo Square"] = 15
    travel_times["Marina District"]["Financial District"] = 17
    travel_times["Marina District"]["Nob Hill"] = 12
    travel_times["Marina District"]["Sunset District"] = 19
    travel_times["Marina District"]["Chinatown"] = 15
    travel_times["Marina District"]["Russian Hill"] = 8
    travel_times["Marina District"]["North Beach"] = 11
    travel_times["Marina District"]["Haight-Ashbury"] = 16
    
    # Financial District travel times
    travel_times["Financial District"]["Union Square"] = 9
    travel_times["Financial District"]["Presidio"] = 22
    travel_times["Financial District"]["Alamo Square"] = 17
    travel_times["Financial District"]["Marina District"] = 15
    travel_times["Financial District"]["Nob Hill"] = 8
    travel_times["Financial District"]["Sunset District"] = 30
    travel_times["Financial District"]["Chinatown"] = 5
    travel_times["Financial District"]["Russian Hill"] = 11
    travel_times["Financial District"]["North Beach"] = 7
    travel_times["Financial District"]["Haight-Ashbury"] = 19
    
    # Nob Hill travel times
    travel_times["Nob Hill"]["Union Square"] = 7
    travel_times["Nob Hill"]["Presidio"] = 17
    travel_times["Nob Hill"]["Alamo Square"] = 11
    travel_times["Nob Hill"]["Marina District"] = 11
    travel_times["Nob Hill"]["Financial District"] = 9
    travel_times["Nob Hill"]["Sunset District"] = 24
    travel_times["Nob Hill"]["Chinatown"] = 6
    travel_times["Nob Hill"]["Russian Hill"] = 5
    travel_times["Nob Hill"]["North Beach"] = 8
    travel_times["Nob Hill"]["Haight-Ashbury"] = 13
    
    # Sunset District travel times
    travel_times["Sunset District"]["Union Square"] = 30
    travel_times["Sunset District"]["Presidio"] = 16
    travel_times["Sunset District"]["Alamo Square"] = 17
    travel_times["Sunset District"]["Marina District"] = 21
    travel_times["Sunset District"]["Financial District"] = 30
    travel_times["Sunset District"]["Nob Hill"] = 27
    travel_times["Sunset District"]["Chinatown"] = 30
    travel_times["Sunset District"]["Russian Hill"] = 24
    travel_times["Sunset District"]["North Beach"] = 28
    travel_times["Sunset District"]["Haight-Ashbury"] = 15
    
    # Chinatown travel times
    travel_times["Chinatown"]["Union Square"] = 7
    travel_times["Chinatown"]["Presidio"] = 19
    travel_times["Chinatown"]["Alamo Square"] = 17
    travel_times["Chinatown"]["Marina District"] = 12
    travel_times["Chinatown"]["Financial District"] = 5
    travel_times["Chinatown"]["Nob Hill"] = 9
    travel_times["Chinatown"]["Sunset District"] = 29
    travel_times["Chinatown"]["Russian Hill"] = 7
    travel_times["Chinatown"]["North Beach"] = 3
    travel_times["Chinatown"]["Haight-Ashbury"] = 19
    
    # Russian Hill travel times
    travel_times["Russian Hill"]["Union Square"] = 10
    travel_times["Russian Hill"]["Presidio"] = 14
    travel_times["Russian Hill"]["Alamo Square"] = 15
    travel_times["Russian Hill"]["Marina District"] = 7
    travel_times["Russian Hill"]["Financial District"] = 11
    travel_times["Russian Hill"]["Nob Hill"] = 5
    travel_times["Russian Hill"]["Sunset District"] = 23
    travel_times["Russian Hill"]["Chinatown"] = 9
    travel_times["Russian Hill"]["North Beach"] = 5
    travel_times["Russian Hill"]["Haight-Ashbury"] = 17
    
    # North Beach travel times
    travel_times["North Beach"]["Union Square"] = 7
    travel_times["North Beach"]["Presidio"] = 17
    travel_times["North Beach"]["Alamo Square"] = 16
    travel_times["North Beach"]["Marina District"] = 9
    travel_times["North Beach"]["Financial District"] = 8
    travel_times["North Beach"]["Nob Hill"] = 7
    travel_times["North Beach"]["Sunset District"] = 27
    travel_times["North Beach"]["Chinatown"] = 6
    travel_times["North Beach"]["Russian Hill"] = 4
    travel_times["North Beach"]["Haight-Ashbury"] = 18
    
    # Haight-Ashbury travel times
    travel_times["Haight-Ashbury"]["Union Square"] = 19
    travel_times["Haight-Ashbury"]["Presidio"] = 15
    travel_times["Haight-Ashbury"]["Alamo Square"] = 5
    travel_times["Haight-Ashbury"]["Marina District"] = 17
    travel_times["Haight-Ashbury"]["Financial District"] = 21
    travel_times["Haight-Ashbury"]["Nob Hill"] = 15
    travel_times["Haight-Ashbury"]["Sunset District"] = 15
    travel_times["Haight-Ashbury"]["Chinatown"] = 19
    travel_times["Haight-Ashbury"]["Russian Hill"] = 17
    travel_times["Haight-Ashbury"]["North Beach"] = 19
    
    # Define friend constraints
    friends = [
        {"name": "Kimberly", "location": "Presidio", "start": "15:30", "end": "16:00", "min_duration": 15},
        {"name": "Elizabeth", "location": "Alamo Square", "start": "19:15", "end": "20:15", "min_duration": 15},
        {"name": "Joshua", "location": "Marina District", "start": "10:30", "end": "14:15", "min_duration": 45},
        {"name": "Sandra", "location": "Financial District", "start": "19:30", "end": "20:15", "min_duration": 45},
        {"name": "Kenneth", "location": "Nob Hill", "start": "12:45", "end": "21:45", "min_duration": 30},
        {"name": "Betty", "location": "Sunset District", "start": "14:00", "end": "19:00", "min_duration": 60},
        {"name": "Deborah", "location": "Chinatown", "start": "17:15", "end": "20:30", "min_duration": 15},
        {"name": "Barbara", "location": "Russian Hill", "start": "17:30", "end": "21:15", "min_duration": 120},
        {"name": "Steven", "location": "North Beach", "start": "17:45", "end": "20:45", "min_duration": 90},
        {"name": "Daniel", "location": "Haight-Ashbury", "start": "18:30", "end": "18:45", "min_duration": 15}
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
    
    # Convert friend times to minutes
    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["start"])
        friend["end_min"] = time_to_minutes(friend["end"])
    
    # Create itinerary using a priority-based scheduling approach
    itinerary = []
    current_time = 0  # 9:00 in minutes
    current_location = "Union Square"
    scheduled = set()
    
    # Helper function to check if we can schedule a friend
    def can_schedule(friend, start_time):
        if friend["name"] in scheduled:
            return False
        if start_time < friend["start_min"]:
            return False
        if start_time + friend["min_duration"] > friend["end_min"]:
            return False
        return True
    
    # Try to schedule all friends
    while len(scheduled) < len(friends):
        best_friend = None
        best_start_time = float('inf')
        best_score = -1
        
        for friend in friends:
            if friend["name"] in scheduled:
                continue
                
            # Calculate travel time
            travel_time = travel_times[current_location][friend["location"]]
            
            # Earliest possible start time considering travel
            earliest_start = current_time + travel_time
            
            # Try to schedule at the earliest possible time
            candidate_start = max(earliest_start, friend["start_min"])
            
            if can_schedule(friend, candidate_start):
                # Calculate a score based on urgency and efficiency
                time_until_deadline = friend["end_min"] - candidate_start
                score = (friend["min_duration"] * 10) - time_until_deadline
                
                if score > best_score or (score == best_score and candidate_start < best_start_time):
                    best_friend = friend
                    best_start_time = candidate_start
                    best_score = score
        
        if best_friend is None:
            # If no friend can be scheduled, try to find any friend we can schedule later
            for friend in friends:
                if friend["name"] in scheduled:
                    continue
                    
                # Try scheduling at their start time
                travel_time = travel_times[current_location][friend["location"]]
                candidate_start = max(current_time + travel_time, friend["start_min"])
                
                if can_schedule(friend, candidate_start):
                    best_friend = friend
                    best_start_time = candidate_start
                    break
        
        if best_friend is None:
            # Still no friend can be scheduled, break to avoid infinite loop
            break
        
        # Schedule the best friend
        travel_time = travel_times[current_location][best_friend["location"]]
        
        # Add travel event if needed
        if travel_time > 0:
            itinerary.append({
                "action": "travel",
                "location": best_friend["location"],
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(current_time + travel_time)
            })
        
        # Add meeting event
        start_time = best_start_time
        end_time = start_time + best_friend["min_duration"]
        
        itinerary.append({
            "action": "meet",
            "location": best_friend["location"],
            "person": best_friend["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        # Update state
        scheduled.add(best_friend["name"])
        current_time = end_time
        current_location = best_friend["location"]
    
    # Create result
    result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()