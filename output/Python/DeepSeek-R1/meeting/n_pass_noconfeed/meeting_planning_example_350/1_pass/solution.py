import itertools
import json

def main():
    # Define travel times in minutes
    travel_times = {
        "Bayview": {
            "Pacific Heights": 23,
            "Mission District": 13,
            "Haight-Ashbury": 19,
            "Financial District": 19
        },
        "Pacific Heights": {
            "Bayview": 22,
            "Mission District": 15,
            "Haight-Ashbury": 11,
            "Financial District": 13
        },
        "Mission District": {
            "Bayview": 15,
            "Pacific Heights": 16,
            "Haight-Ashbury": 12,
            "Financial District": 17
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "Pacific Heights": 12,
            "Mission District": 11,
            "Financial District": 21
        },
        "Financial District": {
            "Bayview": 19,
            "Pacific Heights": 13,
            "Mission District": 17,
            "Haight-Ashbury": 19
        }
    }
    
    # Define friends with availability and meeting duration requirements (in minutes from midnight)
    friends_first_three = [
        {"name": "Mary", "location": "Pacific Heights", "start_avail": 600, "end_avail": 1140, "min_duration": 45},
        {"name": "Betty", "location": "Haight-Ashbury", "start_avail": 435, "end_avail": 1035, "min_duration": 90},
        {"name": "Charles", "location": "Financial District", "start_avail": 675, "end_avail": 900, "min_duration": 120}
    ]
    lisa = {"name": "Lisa", "location": "Mission District", "start_avail": 1230, "end_avail": 1320, "min_duration": 75}
    
    # Helper function to format minutes as "H:MM"
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Start at Bayview at 9:00 AM (540 minutes)
    start_time = 540
    start_location = "Bayview"
    best_schedule = None
    
    # Generate all permutations for the first three friends
    perms = itertools.permutations(friends_first_three)
    for perm in perms:
        current_time = start_time
        current_location = start_location
        schedule = []
        valid = True
        
        # Schedule the three friends in this permutation
        for friend in perm:
            # Travel to friend's location
            travel_time = travel_times[current_location][friend["location"]]
            current_time += travel_time
            
            # Wait if arriving before friend is available
            if current_time < friend["start_avail"]:
                current_time = friend["start_avail"]
            
            # Check if meeting can be scheduled within friend's availability
            meeting_end = current_time + friend["min_duration"]
            if meeting_end > friend["end_avail"]:
                valid = False
                break
                
            # Record meeting
            schedule.append({
                "name": friend["name"],
                "location": friend["location"],
                "start": current_time,
                "end": meeting_end
            })
            current_location = friend["location"]
            current_time = meeting_end
        
        if not valid:
            continue
        
        # Check if Lisa can be scheduled after the last meeting
        travel_time_lisa = travel_times[current_location][lisa["location"]]
        arrival_lisa = current_time + travel_time_lisa
        start_lisa = max(arrival_lisa, lisa["start_avail"])
        if start_lisa + lisa["min_duration"] <= lisa["end_avail"]:
            # Create itinerary including Lisa
            itinerary = []
            for meet in schedule:
                itinerary.append({
                    "action": "meet",
                    "location": meet["location"],
                    "person": meet["name"],
                    "start_time": format_time(meet["start"]),
                    "end_time": format_time(meet["end"])
                })
            itinerary.append({
                "action": "meet",
                "location": lisa["location"],
                "person": lisa["name"],
                "start_time": format_time(start_lisa),
                "end_time": format_time(start_lisa + lisa["min_duration"])
            })
            best_schedule = itinerary
            break
    
    # Output the best schedule found (in JSON format)
    if best_schedule is None:
        # Fallback: if no 4-meeting schedule found, try to schedule as many as possible
        # For simplicity, we assume at least the known working schedule exists
        # But in this problem, we know one exists, so we skip fallback
        result = {"itinerary": []}
    else:
        result = {"itinerary": best_schedule}
    print(json.dumps(result))

if __name__ == "__main__":
    main()