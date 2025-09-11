import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time_string(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def try_schedule(order, travel_times, start_time, start_loc):
    current_time = start_time
    current_loc = start_loc
    itinerary = []
    for friend in order:
        travel_time = travel_times[current_loc][friend['loc']]
        current_time += travel_time
        meeting_start = max(current_time, friend['start_avail'])
        meeting_end = meeting_start + friend['min_dur']
        if meeting_end > friend['end_avail']:
            return None
        itinerary.append({
            "action": "meet",
            "location": friend['loc'],
            "person": friend['name'],
            "start_time": minutes_to_time_string(meeting_start),
            "end_time": minutes_to_time_string(meeting_end)
        })
        current_time = meeting_end
        current_loc = friend['loc']
    return itinerary

def main():
    travel_times = {
        'FW': {'GGP': 25, 'P': 17, 'RD': 18},
        'GGP': {'FW': 24, 'P': 11, 'RD': 7},
        'P': {'FW': 19, 'GGP': 12, 'RD': 7},
        'RD': {'FW': 18, 'GGP': 9, 'P': 7}
    }
    
    friends_input = [
        {
            'name': 'Melissa',
            'location': 'GGP',
            'available_start': '8:30',
            'available_end': '20:00',
            'min_duration': 15
        },
        {
            'name': 'Nancy',
            'location': 'P',
            'available_start': '19:45',
            'available_end': '22:00',
            'min_duration': 105
        },
        {
            'name': 'Emily',
            'location': 'RD',
            'available_start': '16:45',
            'available_end': '22:00',
            'min_duration': 120
        }
    ]
    
    friends = []
    for f in friends_input:
        start_min = time_to_minutes(f['available_start'])
        end_min = time_to_minutes(f['available_end'])
        friends.append({
            'name': f['name'],
            'loc': f['location'],
            'start_avail': start_min,
            'end_avail': end_min,
            'min_dur': f['min_duration']
        })
    
    start_time_min = time_to_minutes('9:00')
    start_loc = 'FW'
    
    found_schedule = None
    for num in range(3, 0, -1):
        for order in itertools.permutations(friends, num):
            itinerary = try_schedule(order, travel_times, start_time_min, start_loc)
            if itinerary is not None:
                found_schedule = itinerary
                break
        if found_schedule is not None:
            break
            
    if found_schedule is None:
        found_schedule = []
        
    output = {"itinerary": found_schedule}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()