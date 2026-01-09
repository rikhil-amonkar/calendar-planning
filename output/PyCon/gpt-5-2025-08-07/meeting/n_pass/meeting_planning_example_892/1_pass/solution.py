import constraint
from datetime import datetime, timedelta
import json

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
    
    # Create problem
    problem = constraint.Problem()
    
    # Add variables for each friend: start time and duration
    for i, friend in enumerate(friends):
        friend_start_min = time_to_minutes(friend["start"])
        friend_end_min = time_to_minutes(friend["end"])
        
        # Start time variable (in minutes since 9:00)
        problem.addVariable(f"start_{i}", range(friend_start_min, friend_end_min - friend["min_duration"] + 1))
        
        # Duration variable (at least min_duration, up to available time)
        max_duration = friend_end_min - friend_start_min
        problem.addVariable(f"duration_{i}", range(friend["min_duration"], max_duration + 1))
    
    # Add constraints to ensure meetings don't overlap and account for travel
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            # Constraint: either meeting i ends before meeting j starts (with travel),
            # or meeting j ends before meeting i starts (with travel)
            def no_overlap(start_i, duration_i, start_j, duration_j, i=i, j=j):
                end_i = start_i + duration_i
                end_j = start_j + duration_j
                
                # Calculate travel time between locations
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                travel_ij = travel_times.get((loc_i, loc_j), 60)  # default 60 if not found
                travel_ji = travel_times.get((loc_j, loc_i), 60)
                
                # Check if meetings can be scheduled without conflict
                option1 = (end_i + travel_ij <= start_j)  # i then j
                option2 = (end_j + travel_ji <= start_i)  # j then i
                
                return option1 or option2
            
            problem.addConstraint(no_overlap, 
                                [f"start_{i}", f"duration_{i}", f"start_{j}", f"duration_{j}"])
    
    # Add constraint to ensure we start at Marina District at 9:00
    # Find Laura (at Embarcadero) and ensure we can travel there from Marina District
    laura_index = next(i for i, f in enumerate(friends) if f["name"] == "Laura")
    travel_to_laura = travel_times[("Marina District", "Embarcadero")]
    
    def start_at_marina(start_laura):
        return start_laura >= travel_to_laura
    
    problem.addConstraint(start_at_marina, [f"start_{laura_index}"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found, create a fallback schedule
        itinerary = []
        current_time = time_to_minutes("9:00")
        
        # Try to schedule meetings in a greedy way
        scheduled_friends = set()
        
        while len(scheduled_friends) < len(friends):
            best_friend = None
            best_start = None
            best_duration = None
            
            for i, friend in enumerate(friends):
                if i in scheduled_friends:
                    continue
                
                friend_start_min = time_to_minutes(friend["start"])
                friend_end_min = time_to_minutes(friend["end"])
                
                # Calculate travel time from current location
                if itinerary:
                    last_location = itinerary[-1]["location"]
                    travel_time = travel_times.get((last_location, friend["location"]), 60)
                else:
                    travel_time = travel_times.get(("Marina District", friend["location"]), 60)
                
                # Find earliest possible start time
                earliest_start = max(current_time + travel_time, friend_start_min)
                
                if earliest_start < friend_end_min:
                    # Calculate maximum possible duration
                    max_possible_duration = friend_end_min - earliest_start
                    duration = min(friend["min_duration"], max_possible_duration)
                    
                    if duration >= friend["min_duration"]:
                        if best_friend is None or earliest_start < best_start:
                            best_friend = i
                            best_start = earliest_start
                            best_duration = duration
            
            if best_friend is None:
                break
                
            friend = friends[best_friend]
            start_time = minutes_to_time(best_start)
            end_time = minutes_to_time(best_start + best_duration)
            
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": start_time,
                "end_time": end_time
            })
            
            scheduled_friends.add(best_friend)
            current_time = best_start + best_duration
        
        result = {"itinerary": itinerary}
    else:
        # Use the first solution found
        solution = solutions[0]
        itinerary = []
        
        # Create itinerary from solution
        meeting_times = []
        for i, friend in enumerate(friends):
            start_time = solution[f"start_{i}"]
            duration = solution[f"duration_{i}"]
            meeting_times.append((start_time, duration, friend))
        
        # Sort by start time
        meeting_times.sort(key=lambda x: x[0])
        
        for start, duration, friend in meeting_times:
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(start + duration)
            })
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()