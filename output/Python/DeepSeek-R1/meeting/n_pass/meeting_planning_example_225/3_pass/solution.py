import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        'Sunset District': {
            'North Beach': 29,
            'Union Square': 30,
            'Alamo Square': 17
        },
        'North Beach': {
            'Sunset District': 29,
            'Union Square': 7,
            'Alamo Square': 16
        },
        'Union Square': {
            'Sunset District': 30,
            'North Beach': 7,
            'Alamo Square': 15
        },
        'Alamo Square': {
            'Sunset District': 17,
            'North Beach': 16,
            'Union Square': 15
        }
    }
    
    friends = [
        {'name': 'Sarah', 'location': 'North Beach', 'start': time_to_minutes("16:00"), 'end': time_to_minutes("18:15"), 'min_duration': 60},
        {'name': 'Jeffrey', 'location': 'Union Square', 'start': time_to_minutes("15:00"), 'end': time_to_minutes("22:00"), 'min_duration': 75},
        {'name': 'Brian', 'location': 'Alamo Square', 'start': time_to_minutes("16:00"), 'end': time_to_minutes("17:30"), 'min_duration': 75}
    ]
    
    start_time = time_to_minutes("9:00")
    start_location = 'Sunset District'
    
    best_itinerary = None
    best_total_duration = 0
    
    for r in range(1, len(friends) + 1):
        for subset in itertools.combinations(friends, r):
            for perm in itertools.permutations(subset):
                current_time = start_time
                current_location = start_location
                itinerary = []
                total_duration = 0
                valid = True
                
                for friend in perm:
                    travel_time = travel_times[current_location][friend['location']]
                    arrive_time = current_time + travel_time
                    meeting_start = max(arrive_time, friend['start'])
                    meeting_end = meeting_start + friend['min_duration']
                    
                    if meeting_end > friend['end']:
                        valid = False
                        break
                    
                    itinerary.append({
                        'action': 'meet',
                        'location': friend['location'],
                        'person': friend['name'],
                        'start_time': minutes_to_time(meeting_start),
                        'end_time': minutes_to_time(meeting_end)
                    })
                    total_duration += friend['min_duration']
                    current_time = meeting_end
                    current_location = friend['location']
                
                if valid and total_duration > best_total_duration:
                    best_total_duration = total_duration
                    best_itinerary = itinerary
    
    if best_itinerary is None:
        best_itinerary = []
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()