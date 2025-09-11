import itertools
import json

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        'Mission District': {'The Castro': 7, 'Nob Hill': 12, 'Presidio': 25, 'Marina District': 19, 'Pacific Heights': 16, 'Golden Gate Park': 17, 'Chinatown': 16, 'Richmond District': 20},
        'The Castro': {'Mission District': 7, 'Nob Hill': 16, 'Presidio': 20, 'Marina District': 21, 'Pacific Heights': 16, 'Golden Gate Park': 11, 'Chinatown': 22, 'Richmond District': 16},
        'Nob Hill': {'Mission District': 13, 'The Castro': 17, 'Presidio': 17, 'Marina District': 11, 'Pacific Heights': 8, 'Golden Gate Park': 17, 'Chinatown': 6, 'Richmond District': 14},
        'Presidio': {'Mission District': 26, 'The Castro': 21, 'Nob Hill': 18, 'Marina District': 11, 'Pacific Heights': 11, 'Golden Gate Park': 12, 'Chinatown': 21, 'Richmond District': 7},
        'Marina District': {'Mission District': 20, 'The Castro': 22, 'Nob Hill': 12, 'Presidio': 10, 'Pacific Heights': 7, 'Golden Gate Park': 18, 'Chinatown': 15, 'Richmond District': 11},
        'Pacific Heights': {'Mission District': 15, 'The Castro': 16, 'Nob Hill': 8, 'Presidio': 11, 'Marina District': 6, 'Golden Gate Park': 15, 'Chinatown': 11, 'Richmond District': 12},
        'Golden Gate Park': {'Mission District': 17, 'The Castro': 13, 'Nob Hill': 20, 'Presidio': 11, 'Marina District': 16, 'Pacific Heights': 16, 'Chinatown': 23, 'Richmond District': 7},
        'Chinatown': {'Mission District': 17, 'The Castro': 22, 'Nob Hill': 9, 'Presidio': 19, 'Marina District': 12, 'Pacific Heights': 10, 'Golden Gate Park': 23, 'Richmond District': 20},
        'Richmond District': {'Mission District': 20, 'The Castro': 16, 'Nob Hill': 17, 'Presidio': 7, 'Marina District': 9, 'Pacific Heights': 10, 'Golden Gate Park': 9, 'Chinatown': 20}
    }
    
    friends = [
        {'name': 'Lisa', 'location': 'The Castro', 'start': time_to_minutes('19:15'), 'end': time_to_minutes('21:15'), 'min_duration': 120},
        {'name': 'Daniel', 'location': 'Nob Hill', 'start': time_to_minutes('8:15'), 'end': time_to_minutes('11:00'), 'min_duration': 15},
        {'name': 'Elizabeth', 'location': 'Presidio', 'start': time_to_minutes('21:15'), 'end': time_to_minutes('22:15'), 'min_duration': 45},
        {'name': 'Steven', 'location': 'Marina District', 'start': time_to_minutes('16:30'), 'end': time_to_minutes('20:45'), 'min_duration': 90},
        {'name': 'Timothy', 'location': 'Pacific Heights', 'start': time_to_minutes('12:00'), 'end': time_to_minutes('18:00'), 'min_duration': 90},
        {'name': 'Ashley', 'location': 'Golden Gate Park', 'start': time_to_minutes('20:45'), 'end': time_to_minutes('21:45'), 'min_duration': 60},
        {'name': 'Kevin', 'location': 'Chinatown', 'start': time_to_minutes('12:00'), 'end': time_to_minutes('19:00'), 'min_duration': 30},
        {'name': 'Betty', 'location': 'Richmond District', 'start': time_to_minutes('13:15'), 'end': time_to_minutes('15:45'), 'min_duration': 30}
    ]
    
    start_time = time_to_minutes('9:00')
    start_location = 'Mission District'
    
    best_count = -1
    best_total_time = -1
    best_itinerary = []
    
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_loc = start_location
        itinerary = []
        met_count = 0
        total_meeting_time = 0
        
        for friend in perm:
            travel_time = travel_times[current_loc][friend['location']]
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, friend['start'])
            if meeting_start >= friend['end']:
                continue
            available_time = friend['end'] - meeting_start
            meeting_duration = min(friend['min_duration'], available_time)
            if meeting_duration <= 0:
                continue
            meeting_end = meeting_start + meeting_duration
            itinerary.append((friend['name'], friend['location'], meeting_start, meeting_end))
            met_count += 1
            total_meeting_time += meeting_duration
            current_time = meeting_end
            current_loc = friend['location']
        
        if met_count > best_count or (met_count == best_count and total_meeting_time > best_total_time):
            best_count = met_count
            best_total_time = total_meeting_time
            best_itinerary = itinerary
    
    result = []
    for name, loc, start, end in best_itinerary:
        result.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    
    output = {"itinerary": result}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()