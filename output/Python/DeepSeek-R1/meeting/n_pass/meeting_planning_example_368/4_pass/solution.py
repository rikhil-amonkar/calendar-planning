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
            "Alamo Square": 13,
            "North Beach": 4,
            "Financial District": 11  # Corrected from 10 to 11
        },
        "Alamo Square": {
            "Bayview": 16,
            "Russian Hill": 13,
            "North Beach": 16,
            "Financial District": 17
        },
        "North Beach": {
            "Bayview": 22,
            "Russian Hill": 4,
            "Alamo Square": 16,
            "Financial District": 7
        },
        "Financial District": {
            "Bayview": 19,
            "Russian Hill": 11,  # Corrected from 10 to 11
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
    best_itinerary = None
    
    for num in range(4, 0, -1):
        for perm in permutations(friends, num):
            current_time = start_time
            current_location = start_location
            total_wait = 0
            itinerary = []
            valid = True
            
            if current_location != perm[0]["location"]:
                travel_duration = travel_times[current_location][perm[0]["location"]]
                depart_time = current_time
                arrival_time = current_time + travel_duration
                itinerary.append({
                    "action": "travel",
                    "from": current_location,
                    "to": perm[0]["location"],
                    "start_time": minutes_to_time(depart_time),
                    "end_time": minutes_to_time(arrival_time)
                })
                current_time = arrival_time
                current_location = perm[0]["location"]
            
            for i, friend in enumerate(perm):
                if current_time < friend["start"]:
                    wait_time = friend["start"] - current_time
                    total_wait += wait_time
                    current_time = friend["start"]
                
                meet_start = current_time
                meet_end = meet_start + friend["min_duration"]
                if meet_end > friend["end"]:
                    valid = False
                    break
                
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(meet_start),
                    "end_time": minutes_to_time(meet_end)
                })
                current_time = meet_end
                current_location = friend["location"]
                
                if i < len(perm) - 1:
                    next_location = perm[i+1]["location"]
                    if current_location != next_location:
                        travel_duration = travel_times[current_location][next_location]
                        depart_time = current_time
                        arrival_time = current_time + travel_duration
                        itinerary.append({
                            "action": "travel",
                            "from": current_location,
                            "to": next_location,
                            "start_time": minutes_to_time(depart_time),
                            "end_time": minutes_to_time(arrival_time)
                        })
                        current_time = arrival_time
                        current_location = next_location
            
            if not valid:
                continue
                
            if current_location != "Bayview":
                travel_duration = travel_times[current_location]["Bayview"]
                depart_time = current_time
                arrival_time = current_time + travel_duration
                if arrival_time > 1260:
                    valid = False
                    continue
                itinerary.append({
                    "action": "travel",
                    "from": current_location,
                    "to": "Bayview",
                    "start_time": minutes_to_time(depart_time),
                    "end_time": minutes_to_time(arrival_time)
                })
            
            if not valid:
                continue
                
            if num > best_num_meetings:
                best_num_meetings = num
                best_itinerary = itinerary
                best_total_wait = total_wait
            elif num == best_num_meetings and total_wait < best_total_wait:
                best_itinerary = itinerary
                best_total_wait = total_wait
                
        if best_num_meetings > 0:
            break
            
    result = {"itinerary": best_itinerary} if best_itinerary is not None else {"itinerary": []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()