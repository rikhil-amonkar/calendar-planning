import json

def format_minutes(m):
    h = m // 60
    min_val = m % 60
    return f"{h}:{min_val:02d}"

def main():
    travel_times = {
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Chinatown'): 20,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Chinatown'): 16,
        ('Union Square', 'The Castro'): 19,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Union Square'): 7
    }
    
    emily = {'name': 'Emily', 'location': 'Alamo Square', 'start_avail': 705, 'end_avail': 915, 'duration': 105}
    barbara = {'name': 'Barbara', 'location': 'Union Square', 'start_avail': 1005, 'end_avail': 1095, 'duration': 60}
    william = {'name': 'William', 'location': 'Chinatown', 'start_avail': 1035, 'end_avail': 1140, 'duration': 105}
    
    start_time = 540
    start_location = 'The Castro'
    
    candidates = []
    evening_friends = [barbara, william]
    emily_options = {'early': 705, 'late': 810}
    
    for friend in evening_friends:
        for option, emily_start in emily_options.items():
            travel_key_start = (start_location, emily['location'])
            if travel_key_start not in travel_times:
                continue
            travel_to_emily = travel_times[travel_key_start]
            leave_start = emily_start - travel_to_emily
            if leave_start < start_time:
                continue
                
            emily_end = emily_start + emily['duration']
            if emily_end > emily['end_avail']:
                continue
                
            travel_key_to_friend = (emily['location'], friend['location'])
            if travel_key_to_friend not in travel_times:
                continue
            travel_to_friend = travel_times[travel_key_to_friend]
            arrive_friend = emily_end + travel_to_friend
            
            meeting_start = max(arrive_friend, friend['start_avail'])
            meeting_end = meeting_start + friend['duration']
            if meeting_end > friend['end_avail']:
                continue
                
            waiting_time = meeting_start - arrive_friend
            itinerary = [
                {
                    'action': 'meet',
                    'location': emily['location'],
                    'person': emily['name'],
                    'start_time': emily_start,
                    'end_time': emily_end
                },
                {
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': meeting_start,
                    'end_time': meeting_end
                }
            ]
            candidates.append((itinerary, waiting_time, meeting_end))
    
    if candidates:
        candidates.sort(key=lambda x: (x[1], x[2]))
        best_itinerary = candidates[0][0]
    else:
        one_candidates = []
        for friend in [emily, barbara, william]:
            travel_key = (start_location, friend['location'])
            if travel_key not in travel_times:
                continue
            travel_duration = travel_times[travel_key]
            earliest_arrival = start_time + travel_duration
            start_meeting = max(earliest_arrival, friend['start_avail'])
            end_meeting = start_meeting + friend['duration']
            if end_meeting <= friend['end_avail']:
                itinerary = [
                    {
                        'action': 'meet',
                        'location': friend['location'],
                        'person': friend['name'],
                        'start_time': start_meeting,
                        'end_time': end_meeting
                    }
                ]
                one_candidates.append((itinerary, end_meeting))
        if one_candidates:
            one_candidates.sort(key=lambda x: x[1])
            best_itinerary = one_candidates[0][0]
        else:
            best_itinerary = []
    
    formatted_itinerary = []
    for event in best_itinerary:
        formatted_event = event.copy()
        formatted_event['start_time'] = format_minutes(formatted_event['start_time'])
        formatted_event['end_time'] = format_minutes(formatted_event['end_time'])
        formatted_itinerary.append(formatted_event)
        
    result = {"itinerary": formatted_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()