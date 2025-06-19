import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    friends_info = [
        {"name": "Betty", "location": "Embarcadero", "available_start": "19:45", "available_end": "21:45", "min_duration": 15},
        {"name": "Karen", "location": "Fisherman's Wharf", "available_start": "8:45", "available_end": "15:00", "min_duration": 30},
        {"name": "Anthony", "location": "Financial District", "available_start": "9:15", "available_end": "21:30", "min_duration": 105}
    ]
    
    for friend in friends_info:
        friend['available_start'] = time_to_minutes(friend['available_start'])
        friend['available_end'] = time_to_minutes(friend['available_end'])
    
    travel_times = {
        'Bayview': {'Embarcadero': 21, 'Fisherman\'s Wharf': 25, 'Financial District': 19},
        'Embarcadero': {'Bayview': 21, 'Fisherman\'s Wharf': 6, 'Financial District': 5},
        'Fisherman\'s Wharf': {'Bayview': 25, 'Embarcadero': 6, 'Financial District': 10},
        'Financial District': {'Bayview': 19, 'Embarcadero': 5, 'Fisherman\'s Wharf': 10}
    }
    
    start_location = "Bayview"
    start_time_minutes = time_to_minutes("9:00")
    
    best_itinerary = None
    best_count = 0
    best_travel = float('inf')
    all_friends = friends_info
    
    for r in range(len(all_friends), 0, -1):
        for subset in itertools.combinations(all_friends, r):
            for perm in itertools.permutations(subset):
                current_location = start_location
                current_time = start_time_minutes
                itinerary = []
                count = 0
                total_travel = 0
                feasible = True
                
                for friend in perm:
                    try:
                        travel = travel_times[current_location][friend['location']]
                    except KeyError:
                        feasible = False
                        break
                    
                    immediate_arrival = current_time + travel
                    arrival = max(immediate_arrival, friend['available_start'])
                    start_meeting = arrival
                    end_meeting = start_meeting + friend['min_duration']
                    
                    if end_meeting > friend['available_end']:
                        feasible = False
                        break
                    
                    itinerary.append({
                        "action": "meet",
                        "location": friend['location'],
                        "person": friend['name'],
                        "start_time": minutes_to_time(start_meeting),
                        "end_time": minutes_to_time(end_meeting)
                    })
                    total_travel += travel
                    current_time = end_meeting
                    current_location = friend['location']
                    count += 1
                
                if feasible:
                    if count > best_count or (count == best_count and total_travel < best_travel):
                        best_count = count
                        best_travel = total_travel
                        best_itinerary = itinerary
        if best_count == r:
            break
    
    if best_itinerary is None:
        best_itinerary = []
        
    result = {"itinerary": best_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()