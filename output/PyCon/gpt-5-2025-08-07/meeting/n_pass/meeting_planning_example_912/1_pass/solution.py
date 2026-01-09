import constraint
from datetime import datetime, timedelta
import json

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
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time for each meeting (in minutes from 9:00)
    for friend in friends:
        # Meeting must start within friend's availability window
        # and end before friend's end time
        earliest_start = friend["start_min"]
        latest_start = friend["end_min"] - friend["min_duration"]
        problem.addVariable(friend["name"], range(earliest_start, latest_start + 1))
    
    # Add travel time constraints
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            friend1 = friends[i]
            friend2 = friends[j]
            
            # If we meet friend1 then friend2, we need travel time
            def travel_constraint(time1, time2):
                # If meetings don't overlap in time, check travel
                if time1 + friend1["min_duration"] <= time2:
                    travel_needed = travel_times[friend1["location"]][friend2["location"]]
                    return time1 + friend1["min_duration"] + travel_needed <= time2
                elif time2 + friend2["min_duration"] <= time1:
                    travel_needed = travel_times[friend2["location"]][friend1["location"]]
                    return time2 + friend2["min_duration"] + travel_needed <= time1
                else:
                    # Meetings overlap, which is impossible
                    return False
            
            problem.addConstraint(travel_constraint, [friend1["name"], friend2["name"]])
    
    # Try to find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found, try a simpler approach with fewer constraints
        # This is a fallback for when the full constraint solving fails
        itinerary = []
        
        # Start at Union Square at 9:00
        current_time = time_to_minutes("9:00")
        current_location = "Union Square"
        
        # Try to schedule meetings in a greedy way
        scheduled_friends = []
        
        # Sort friends by end time (earlier first)
        sorted_friends = sorted(friends, key=lambda x: x["end_min"])
        
        for friend in sorted_friends:
            # Calculate travel time to friend's location
            travel_time = travel_times[current_location][friend["location"]]
            
            # Earliest we can start meeting
            earliest_possible_start = current_time + travel_time
            
            # Check if we can fit the meeting
            if (earliest_possible_start >= friend["start_min"] and 
                earliest_possible_start + friend["min_duration"] <= friend["end_min"]):
                
                # Schedule the meeting
                start_time = max(earliest_possible_start, friend["start_min"])
                end_time = start_time + friend["min_duration"]
                
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                
                # Update current time and location
                current_time = end_time
                current_location = friend["location"]
                scheduled_friends.append(friend["name"])
        
        # Create result
        result = {"itinerary": itinerary}
        
    else:
        # Use the first solution found
        solution = solutions[0]
        
        # Create itinerary from solution
        itinerary_events = []
        for friend in friends:
            start_time = solution[friend["name"]]
            end_time = start_time + friend["min_duration"]
            
            itinerary_events.append({
                "friend": friend["name"],
                "location": friend["location"],
                "start_time": start_time,
                "end_time": end_time
            })
        
        # Sort by start time
        itinerary_events.sort(key=lambda x: x["start_time"])
        
        # Convert to final format
        itinerary = []
        for event in itinerary_events:
            itinerary.append({
                "action": "meet",
                "location": event["location"],
                "person": event["friend"],
                "start_time": minutes_to_time(event["start_time"]),
                "end_time": minutes_to_time(event["end_time"])
            })
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()