import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = [
        "Embarcadero", "Fisherman's Wharf", "Financial District", "Russian Hill", "Marina District",
        "Richmond District", "Pacific Heights", "Haight-Ashbury", "Presidio", "Nob Hill", "The Castro"
    ]
    
    # Travel time matrix (in minutes)
    travel_times = {
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "The Castro"): 20,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "The Castro"): 21,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "The Castro"): 22,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "The Castro"): 16,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "The Castro"): 16,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "The Castro"): 21,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "The Castro"): 17,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Nob Hill"): 16
    }
    
    # Friend constraints
    friends = [
        {"name": "Stephanie", "location": "Fisherman's Wharf", "start": "15:30", "end": "22:00", "min_duration": 30},
        {"name": "Lisa", "location": "Financial District", "start": "10:45", "end": "17:15", "min_duration": 15},
        {"name": "Melissa", "location": "Russian Hill", "start": "17:00", "end": "21:45", "min_duration": 120},
        {"name": "Betty", "location": "Marina District", "start": "10:45", "end": "14:15", "min_duration": 60},
        {"name": "Sarah", "location": "Richmond District", "start": "16:15", "end": "19:30", "min_duration": 105},
        {"name": "Daniel", "location": "Pacific Heights", "start": "18:30", "end": "21:45", "min_duration": 60},
        {"name": "Joshua", "location": "Haight-Ashbury", "start": "9:00", "end": "15:30", "min_duration": 15},
        {"name": "Joseph", "location": "Presidio", "start": "7:00", "end": "13:00", "min_duration": 45},
        {"name": "Andrew", "location": "Nob Hill", "start": "19:45", "end": "22:00", "min_duration": 105},
        {"name": "John", "location": "The Castro", "start": "13:15", "end": "19:45", "min_duration": 45}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, "%H:%M")
        base_time = datetime.strptime("9:00", "%H:%M")
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)
    
    # Convert minutes to time string
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
        min_duration = friend["min_duration"]
        
        # Start time variable (in minutes from 9:00)
        problem.addVariable(f"start_{i}", range(friend_start_min, friend_end_min - min_duration + 1))
        
        # Duration variable (at least min_duration, up to available time)
        problem.addVariable(f"duration_{i}", range(min_duration, friend_end_min - friend_start_min + 1))
    
    # Add constraint to ensure meetings don't overlap and account for travel
    def no_overlap_constraint(*args):
        # Group variables by friend
        friend_meetings = []
        for i in range(len(friends)):
            start_idx = i * 2
            duration_idx = i * 2 + 1
            friend_meetings.append((args[start_idx], args[duration_idx], i))
        
        # Sort by start time
        friend_meetings.sort()
        
        # Check for overlaps considering travel time
        for j in range(len(friend_meetings) - 1):
            current_start, current_duration, current_idx = friend_meetings[j]
            next_start, next_duration, next_idx = friend_meetings[j + 1]
            
            current_end = current_start + current_duration
            current_location = friends[current_idx]["location"]
            next_location = friends[next_idx]["location"]
            
            # Travel time between locations
            travel_time = travel_times.get((current_location, next_location), 30)  # Default 30 min if not found
            
            if current_end + travel_time > next_start:
                return False
        
        return True
    
    # Get all variable names for the constraint
    all_vars = []
    for i in range(len(friends)):
        all_vars.append(f"start_{i}")
        all_vars.append(f"duration_{i}")
    
    problem.addConstraint(no_overlap_constraint, all_vars)
    
    # Objective: maximize total meeting time
    def objective_function(*args):
        total_duration = 0
        for i in range(len(friends)):
            duration_idx = i * 2 + 1
            total_duration += args[duration_idx]
        return total_duration
    
    # Find solution
    solution = problem.getSolution()
    
    if not solution:
        # Fallback: try to meet as many friends as possible with minimum duration
        itinerary = []
        current_time = 0  # 9:00
        current_location = "Embarcadero"
        
        # Sort friends by availability and try to schedule them
        available_friends = []
        for friend in friends:
            start_min = time_to_minutes(friend["start"])
            end_min = time_to_minutes(friend["end"])
            min_duration = friend["min_duration"]
            
            if start_min >= current_time:
                available_friends.append((friend, start_min, end_min, min_duration))
        
        # Sort by start time
        available_friends.sort(key=lambda x: x[1])
        
        for friend_data in available_friends:
            friend, start_min, end_min, min_duration = friend_data
            
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend["location"]), 30)
            
            # Arrival time at friend's location
            arrival_time = current_time + travel_time
            
            # Check if we can meet this friend
            if arrival_time <= end_min - min_duration:
                # Schedule the meeting
                meeting_start = max(arrival_time, start_min)
                meeting_end = meeting_start + min_duration
                
                if meeting_end <= end_min:
                    itinerary.append({
                        "action": "meet",
                        "location": friend["location"],
                        "person": friend["name"],
                        "start_time": minutes_to_time(meeting_start),
                        "end_time": minutes_to_time(meeting_end)
                    })
                    
                    current_time = meeting_end
                    current_location = friend["location"]
    else:
        # Build itinerary from solution
        itinerary = []
        current_time = 0
        current_location = "Embarcadero"
        
        # Get all meetings from solution
        meetings = []
        for i in range(len(friends)):
            start_time = solution[f"start_{i}"]
            duration = solution[f"duration_{i}"]
            meetings.append((start_time, duration, i))
        
        # Sort by start time
        meetings.sort()
        
        for start_time, duration, friend_idx in meetings:
            friend = friends[friend_idx]
            
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend["location"]), 30)
            
            # Arrival time
            arrival_time = current_time + travel_time
            
            # If we arrive after the scheduled start, adjust
            actual_start = max(arrival_time, start_time)
            actual_end = actual_start + duration
            
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(actual_start),
                "end_time": minutes_to_time(actual_end)
            })
            
            current_time = actual_end
            current_location = friend["location"]
    
    # Output result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()