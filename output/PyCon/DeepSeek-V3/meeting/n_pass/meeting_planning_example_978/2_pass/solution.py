import json
from datetime import datetime, timedelta

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
        ("Richiod District", "Haight-Ashbury"): 10,
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
    
    # Preprocess friend data
    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["start"])
        friend["end_min"] = time_to_minutes(friend["end"])
    
    # Greedy scheduling with backtracking
    def schedule_meetings(current_time, current_location, remaining_friends, current_itinerary, best_solution):
        if len(current_itinerary) > len(best_solution["itinerary"]):
            best_solution["itinerary"] = current_itinerary.copy()
            best_solution["total_friends"] = len(current_itinerary)
        
        if not remaining_friends:
            return
        
        # Try each remaining friend
        for i, friend in enumerate(remaining_friends):
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend["location"]), 30)
            
            # Arrival time
            arrival_time = current_time + travel_time
            
            # Check if we can meet this friend
            if arrival_time <= friend["end_min"] - friend["min_duration"]:
                # Schedule the meeting
                meeting_start = max(arrival_time, friend["start_min"])
                meeting_end = meeting_start + friend["min_duration"]
                
                if meeting_end <= friend["end_min"]:
                    # Add to itinerary
                    new_meeting = {
                        "action": "meet",
                        "location": friend["location"],
                        "person": friend["name"],
                        "start_time": minutes_to_time(meeting_start),
                        "end_time": minutes_to_time(meeting_end)
                    }
                    
                    # Recursively schedule remaining friends
                    new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                    schedule_meetings(meeting_end, friend["location"], new_remaining, 
                                    current_itinerary + [new_meeting], best_solution)
    
    # Start scheduling from Embarcadero at 9:00
    start_time = 0  # 9:00 in minutes
    start_location = "Embarcadero"
    
    best_solution = {"itinerary": [], "total_friends": 0}
    
    # Try different orderings to find best solution
    import itertools
    
    # Limit permutations to avoid combinatorial explosion
    friend_permutations = list(itertools.permutations(friends, min(6, len(friends))))
    
    for perm in friend_permutations[:50]:  # Limit to first 50 permutations
        schedule_meetings(start_time, start_location, list(perm), [], best_solution)
        if best_solution["total_friends"] == len(friends):
            break  # Found optimal solution
    
    # If no solution found with all friends, try a simpler greedy approach
    if not best_solution["itinerary"]:
        itinerary = []
        current_time = start_time
        current_location = start_location
        
        # Sort friends by end time (earlier first)
        sorted_friends = sorted(friends, key=lambda x: x["end_min"])
        
        for friend in sorted_friends:
            travel_time = travel_times.get((current_location, friend["location"]), 30)
            arrival_time = current_time + travel_time
            
            if arrival_time <= friend["end_min"] - friend["min_duration"]:
                meeting_start = max(arrival_time, friend["start_min"])
                meeting_end = meeting_start + friend["min_duration"]
                
                if meeting_end <= friend["end_min"]:
                    itinerary.append({
                        "action": "meet",
                        "location": friend["location"],
                        "person": friend["name"],
                        "start_time": minutes_to_time(meeting_start),
                        "end_time": minutes_to_time(meeting_end)
                    })
                    
                    current_time = meeting_end
                    current_location = friend["location"]
        
        best_solution["itinerary"] = itinerary
    
    # Output result
    result = {"itinerary": best_solution["itinerary"]}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()