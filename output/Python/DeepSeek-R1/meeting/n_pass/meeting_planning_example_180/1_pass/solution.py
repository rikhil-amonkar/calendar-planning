import json
from itertools import permutations

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

def main():
    travel_times = {
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'The Castro'): 22,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'The Castro'): 7,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Mission District'): 7
    }
    
    friends = [
        {'name': 'James', 'location': 'Mission District', 'start': time_to_minutes('12:45'), 'end': time_to_minutes('14:00'), 'min_duration': 75},
        {'name': 'Robert', 'location': 'The Castro', 'start': time_to_minutes('12:45'), 'end': time_to_minutes('15:15'), 'min_duration': 30}
    ]
    
    start_location = 'North Beach'
    start_time = time_to_minutes('9:00')
    
    best_schedule = None
    best_count = 0
    perms = list(permutations([0, 1]))
    
    for perm in perms:
        current_loc = start_location
        current_time_val = start_time
        schedule = []
        valid = True
        
        for idx in perm:
            friend = friends[idx]
            travel_key = (current_loc, friend['location'])
            if travel_key not in travel_times:
                valid = False
                break
            travel_duration = travel_times[travel_key]
            arrival = current_time_val + travel_duration
            meeting_start = max(arrival, friend['start'])
            meeting_end = meeting_start + friend['min_duration']
            if meeting_end > friend['end']:
                valid = False
                break
            schedule.append((friend['name'], friend['location'], meeting_start, meeting_end))
            current_loc = friend['location']
            current_time_val = meeting_end
        
        if valid:
            best_schedule = schedule
            best_count = 2
            break
    
    if best_schedule is None:
        for idx in [0, 1]:
            friend = friends[idx]
            travel_key = (start_location, friend['location'])
            if travel_key in travel_times:
                travel_duration = travel_times[travel_key]
                arrival = start_time + travel_duration
                meeting_start = max(arrival, friend['start'])
                meeting_end = meeting_start + friend['min_duration']
                if meeting_end <= friend['end']:
                    best_schedule = [(friend['name'], friend['location'], meeting_start, meeting_end)]
                    best_count = 1
                    break
    
    itinerary = []
    if best_schedule:
        for meeting in best_schedule:
            name, location, start_min, end_min = meeting
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(start_min),
                "end_time": minutes_to_time(end_min)
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()