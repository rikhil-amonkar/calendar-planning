import itertools
import json

def main():
    # Define friends with their constraints: (name, location, available_start_min, available_end_min, min_duration_min)
    friends = [
        ("Carol", "Sunset District", 10*60+15, 11*60+45, 30),
        ("Karen", "Bayview", 12*60+45, 15*60, 120),
        ("Rebecca", "Mission District", 11*60+30, 20*60+15, 120)
    ]
    
    # Travel times in minutes: travel_times[from][to]
    travel_times = {
        "Union Square": {"Mission District": 14, "Bayview": 15, "Sunset District": 26},
        "Mission District": {"Union Square": 15, "Bayview": 15, "Sunset District": 24},
        "Bayview": {"Union Square": 17, "Mission District": 13, "Sunset District": 23},
        "Sunset District": {"Union Square": 30, "Mission District": 24, "Bayview": 22}
    }
    
    # Generate all permutations of the friends
    perms = list(itertools.permutations(friends))
    best_itinerary = None
    best_count = 0
    
    for perm in perms:
        current_location = "Union Square"
        current_time = 540  # 9:00 AM in minutes (9*60)
        itinerary_perm = []
        
        for friend in perm:
            name, loc, avail_start, avail_end, min_dur = friend
            # Travel to the friend's location
            travel_duration = travel_times[current_location][loc]
            current_time += travel_duration  # Arrival time at friend's location
            
            # Calculate meeting start and end times
            start_meeting = max(current_time, avail_start)
            end_meeting = start_meeting + min_dur
            
            # Check if meeting fits within the friend's availability
            if end_meeting <= avail_end:
                itinerary_perm.append((name, loc, start_meeting, end_meeting))
                current_time = end_meeting  # Update time after the meeting
            # Update current location regardless of meeting
            current_location = loc
        
        # Update best itinerary if this permutation has more meetings
        if len(itinerary_perm) > best_count:
            best_count = len(itinerary_perm)
            best_itinerary = itinerary_perm
            # Break early if all 3 meetings are scheduled (optimization)
            if best_count == 3:
                break
    
    # Convert best itinerary to the required JSON format
    result = []
    if best_itinerary:
        for meeting in best_itinerary:
            name, loc, start_min, end_min = meeting
            # Format time from minutes to "H:MM"
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
            result.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    
    # Output the itinerary as JSON
    output = {"itinerary": result}
    print(json.dumps(output))

if __name__ == "__main__":
    main()