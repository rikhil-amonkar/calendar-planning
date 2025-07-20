import itertools
import json

def min_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    mins = total_minutes % 60
    return f"{hours}:{mins:02}"

def main():
    travel_times = {
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Financial District"): 23,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Financial District"): 22,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Richmond District"): 21
    }
    
    friends = [
        {"name": "Emily", "location": "Presidio", "start": 435, "end": 720, "min_duration": 105},
        {"name": "Joseph", "location": "Richmond District", "start": 495, "end": 780, "min_duration": 120},
        {"name": "Melissa", "location": "Financial District", "start": 405, "end": 765, "min_duration": 75}
    ]
    
    all_indices = [0, 1, 2]
    
    # Try all permutations for three friends
    for perm in itertools.permutations(all_indices):
        itinerary = []
        current_time = 0
        current_loc = "Fisherman's Wharf"
        valid = True
        
        for idx in perm:
            friend = friends[idx]
            travel_key = (current_loc, friend["location"])
            travel_duration = travel_times.get(travel_key)
            if travel_duration is None:
                valid = False
                break
                
            arrival_time = current_time + travel_duration
            start_meeting = max(arrival_time, friend["start"])
            end_meeting = start_meeting + friend["min_duration"]
            
            if end_meeting > friend["end"]:
                valid = False
                break
                
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": min_to_time(start_meeting),
                "end_time": min_to_time(end_meeting)
            })
            
            current_time = end_meeting
            current_loc = friend["location"]
        
        if valid:
            print(json.dumps({"itinerary": itinerary}))
            return
    
    # Try subsets of two friends
    for subset in itertools.combinations(all_indices, 2):
        for perm in itertools.permutations(subset):
            itinerary = []
            current_time = 0
            current_loc = "Fisherman's Wharf"
            valid = True
            
            for idx in perm:
                friend = friends[idx]
                travel_key = (current_loc, friend["location"])
                travel_duration = travel_times.get(travel_key)
                if travel_duration is None:
                    valid = False
                    break
                    
                arrival_time = current_time + travel_duration
                start_meeting = max(arrival_time, friend["start"])
                end_meeting = start_meeting + friend["min_duration"]
                
                if end_meeting > friend["end"]:
                    valid = False
                    break
                    
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": min_to_time(start_meeting),
                    "end_time": min_to_time(end_meeting)
                })
                
                current_time = end_meeting
                current_loc = friend["location"]
            
            if valid:
                print(json.dumps({"itinerary": itinerary}))
                return
    
    # Try each friend individually
    for idx in all_indices:
        friend = friends[idx]
        travel_key = ("Fisherman's Wharf", friend["location"])
        travel_duration = travel_times.get(travel_key)
        if travel_duration is None:
            continue
            
        arrival_time = 0 + travel_duration
        start_meeting = max(arrival_time, friend["start"])
        end_meeting = start_meeting + friend["min_duration"]
        
        if end_meeting > friend["end"]:
            continue
            
        itinerary = [{
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": min_to_time(start_meeting),
            "end_time": min_to_time(end_meeting)
        }]
        
        print(json.dumps({"itinerary": itinerary}))
        return
    
    # If no meetings possible, output empty itinerary
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()