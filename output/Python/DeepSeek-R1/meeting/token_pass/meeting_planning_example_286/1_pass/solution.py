import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        'Union Square': {
            'Mission District': 14,
            'Bayview': 15,
            'Sunset District': 26
        },
        'Mission District': {
            'Union Square': 15,
            'Bayview': 15,
            'Sunset District': 24
        },
        'Bayview': {
            'Union Square': 17,
            'Mission District': 13,
            'Sunset District': 23
        },
        'Sunset District': {
            'Union Square': 30,
            'Mission District': 24,
            'Bayview': 22
        }
    }
    
    meetings = [
        {
            'person': 'Rebecca',
            'location': 'Mission District',
            'window_start': time_to_minutes('11:30'),
            'window_end': time_to_minutes('20:15'),
            'min_duration': 120
        },
        {
            'person': 'Karen',
            'location': 'Bayview',
            'window_start': time_to_minutes('12:45'),
            'window_end': time_to_minutes('15:00'),
            'min_duration': 120
        },
        {
            'person': 'Carol',
            'location': 'Sunset District',
            'window_start': time_to_minutes('10:15'),
            'window_end': time_to_minutes('11:45'),
            'min_duration': 30
        }
    ]
    
    start_time = time_to_minutes('9:00')
    start_location = 'Union Square'
    
    best_itinerary = []
    best_meetings_count = 0
    
    for order in permutations(meetings):
        current_time = start_time
        current_location = start_location
        itinerary = []
        valid = True
        
        for meeting in order:
            travel_time = travel_times[current_location][meeting['location']]
            arrival_time = current_time + travel_time
            
            start_meeting = max(arrival_time, meeting['window_start'])
            end_meeting = start_meeting + meeting['min_duration']
            
            if end_meeting > meeting['window_end']:
                valid = False
                break
                
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['person'],
                'start_time': minutes_to_time(start_meeting),
                'end_time': minutes_to_time(end_meeting)
            })
            
            current_time = end_meeting
            current_location = meeting['location']
        
        if valid and len(itinerary) > best_meetings_count:
            best_meetings_count = len(itinerary)
            best_itinerary = itinerary
    
    result = {
        "itinerary": best_itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()