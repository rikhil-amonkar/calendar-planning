import json
import itertools
from itertools import permutations

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    travel_times = {
        "Bayview": {
            "Russian Hill": 23,
            "Alamo Square": 16,
            "North Beach": 21,
            "Financial District": 19
        },
        "Russian Hill": {
            "Bayview": 23,
            "Alamo Square": 15,
            "North Beach": 5,
            "Financial District": 11
        },
        "Alamo Square": {
            "Bayview": 16,
            "Russian Hill": 13,
            "North Beach": 15,
            "Financial District": 17
        },
        "North Beach": {
            "Bayview": 22,
            "Russian Hill": 4,
            "Alamo Square": 16,
            "Financial District": 8
        },
        "Financial District": {
            "Bayview": 19,
            "Russian Hill": 10,
            "Alamo Square": 17,
            "North Beach": 7
        }
    }
    
    friends = [
        {"name": "Joseph", "location": "Russian Hill", "start": 510, "end": 1155, "min_duration": 60},
        {"name": "Nancy", "location": "Alamo Square", "start": 660, "end": 960, "min_duration": 90},
        {"name": "Jason", "location": "North Beach", "start": 1005, "end": 1305, "min_duration": 15},
        {"name": "Jeffrey", "location": "Financial District", "start": 630, "end": 945, "min_duration": 45}
    ]
    
    start_time = 540
    start_location = "Bayview"
    
    best_num_meetings = 0
    best_total_wait = float('inf')
    best_schedule = None
    best_perm = None
    
    for num in range(4, 0, -1):
        for perm in permutations(friends, num):
            current_time = start_time
            current_location = start_location
            total_wait = 0
            schedule = []
            valid = True
            
            for friend in perm:
                if current_location != friend["location"]:
                    travel_time = travel_times[current_location][friend["location"]]
                else:
                    travel_time = 0
                
                # Calculate earliest possible arrival time if leaving immediately
                earliest_arrival = current_time + travel_time
                # We can choose to arrive later to avoid waiting, but not earlier than earliest_arrival
                # The best arrival time to minimize waiting is max(earliest_arrival, friend["start"])
                arrival_time = max(earliest_arrival, friend["start"])
                # Waiting only occurs if we arrive before friend's start time
                wait_time = max(0, friend["start"] - earliest_arrival)
                start_meeting = arrival_time
                end_meeting = start_meeting + friend["min_duration"]
                
                if end_meeting > friend["end"]:
                    valid = False
                    break
                    
                total_wait += wait_time
                schedule.append({
                    "friend": friend,
                    "start": start_meeting,
                    "end": end_meeting
                })
                current_time = end_meeting
                current_location = friend["location"]
            
            if not valid:
                continue
                
            if num > best_num_meetings:
                best_num_meetings = num
                best_schedule = schedule
                best_total_wait = total_wait
                best_perm = perm
            elif num == best_num_meetings and total_wait < best_total_wait:
                best_schedule = schedule
                best_total_wait = total_wait
                best_perm = perm
        
        if best_num_meetings > 0:
            break
            
    itinerary = []
    if best_schedule is not None:
        for meeting in best_schedule:
            friend = meeting["friend"]
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
    
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()