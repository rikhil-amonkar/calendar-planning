import itertools
import json

def main():
    # Define travel times between locations (in minutes)
    travel_times = {
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Pacific Heights": 13,
            "Mission District": 17
        },
        "Fisherman's Wharf": {
            "Financial District": 11,
            "Pacific Heights": 12,
            "Mission District": 22
        },
        "Pacific Heights": {
            "Financial District": 13,
            "Fisherman's Wharf": 13,
            "Mission District": 15
        },
        "Mission District": {
            "Financial District": 17,
            "Fisherman's Wharf": 22,
            "Pacific Heights": 16
        }
    }
    
    # Define friends with their constraints (times in minutes since midnight)
    friends = [
        {
            "name": "David",
            "location": "Fisherman's Wharf",
            "start_avail": 10 * 60 + 45,  # 10:45 -> 645
            "end_avail": 15 * 60 + 30,     # 15:30 -> 930
            "min_time": 15
        },
        {
            "name": "Timothy",
            "location": "Pacific Heights",
            "start_avail": 9 * 60,         # 9:00 -> 540
            "end_avail": 15 * 60 + 30,     # 15:30 -> 930
            "min_time": 75
        },
        {
            "name": "Robert",
            "location": "Mission District",
            "start_avail": 12 * 60 + 15,   # 12:15 -> 735
            "end_avail": 19 * 60 + 45,     # 19:45 -> 1185
            "min_time": 90
        }
    ]
    
    # Helper function to format minutes since midnight to "H:MM" string
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    start_time = 9 * 60  # 9:00 AM in minutes (540)
    start_location = "Financial District"
    permutations = list(itertools.permutations([0, 1, 2]))  # Permutations of friend indices
    
    best_itinerary = None
    best_num_met = 0
    best_total_waiting = float('inf')
    
    for perm in permutations:
        current_time = start_time
        current_location = start_location
        itinerary = []
        total_waiting = 0
        num_met = 0
        
        for idx in perm:
            friend = friends[idx]
            # Travel to the friend's location
            travel_duration = travel_times[current_location][friend["location"]]
            current_time += travel_duration
            current_location = friend["location"]
            
            # Calculate meeting start and end times
            start_meeting = max(current_time, friend["start_avail"])
            if current_time < friend["start_avail"]:
                total_waiting += (friend["start_avail"] - current_time)
            end_meeting = start_meeting + friend["min_time"]
            
            # Check if meeting is feasible within friend's availability
            if end_meeting <= friend["end_avail"]:
                # Add meeting to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": format_time(start_meeting),
                    "end_time": format_time(end_meeting)
                })
                num_met += 1
                current_time = end_meeting  # Update time after meeting
        
        # Update best itinerary if this permutation is better
        if num_met > best_num_met:
            best_num_met = num_met
            best_itinerary = itinerary
            best_total_waiting = total_waiting
        elif num_met == best_num_met and total_waiting < best_total_waiting:
            best_itinerary = itinerary
            best_total_waiting = total_waiting
    
    # Prepare result dictionary
    result = {"itinerary": best_itinerary if best_itinerary else []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()