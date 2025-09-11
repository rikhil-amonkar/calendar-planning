import itertools
import json

def main():
    # Define travel times between districts (in minutes)
    travel_times = {
        'Marina District': {
            'Mission District': 20,
            'Fisherman\'s Wharf': 10,
            'Presidio': 10,
            'Union Square': 16,
            'Sunset District': 19,
            'Financial District': 17,
            'Haight-Ashbury': 16,
            'Russian Hill': 8
        },
        'Mission District': {
            'Marina District': 19,
            'Fisherman\'s Wharf': 22,
            'Presidio': 25,
            'Union Square': 15,
            'Sunset District': 24,
            'Financial District': 15,
            'Haight-Ashbury': 12,
            'Russian Hill': 15
        },
        'Fisherman\'s Wharf': {
            'Marina District': 9,
            'Mission District': 22,
            'Presidio': 17,
            'Union Square': 13,
            'Sunset District': 27,
            'Financial District': 11,
            'Haight-Ashbury': 22,
            'Russian Hill': 7
        },
        'Presidio': {
            'Marina District': 11,
            'Mission District': 26,
            'Fisherman\'s Wharf': 19,
            'Union Square': 22,
            'Sunset District': 15,
            'Financial District': 23,
            'Haight-Ashbury': 15,
            'Russian Hill': 14
        },
        'Union Square': {
            'Marina District': 18,
            'Mission District': 14,
            'Fisherman\'s Wharf': 15,
            'Presidio': 24,
            'Sunset District': 27,
            'Financial District': 9,
            'Haight-Ashbury': 18,
            'Russian Hill': 13
        },
        'Sunset District': {
            'Marina District': 21,
            'Mission District': 25,
            'Fisherman\'s Wharf': 29,
            'Presidio': 16,
            'Union Square': 30,
            'Financial District': 30,
            'Haight-Ashbury': 15,
            'Russian Hill': 24
        },
        'Financial District': {
            'Marina District': 15,
            'Mission District': 17,
            'Fisherman\'s Wharf': 10,
            'Presidio': 22,
            'Union Square': 9,
            'Sunset District': 30,
            'Haight-Ashbury': 19,
            'Russian Hill': 11
        },
        'Haight-Ashbury': {
            'Marina District': 17,
            'Mission District': 11,
            'Fisherman\'s Wharf': 23,
            'Presidio': 15,
            'Union Square': 19,
            'Sunset District': 15,
            'Financial District': 21,
            'Russian Hill': 17
        },
        'Russian Hill': {
            'Marina District': 7,
            'Mission District': 16,
            'Fisherman\'s Wharf': 7,
            'Presidio': 14,
            'Union Square': 10,
            'Sunset District': 23,
            'Financial District': 11,
            'Haight-Ashbury': 17
        }
    }
    
    # Define meetings with constraints (times converted to minutes from 9:00 AM)
    meetings = [
        {'person': 'Karen', 'location': 'Mission District', 'start_avail': 855, 'end_avail': 1320, 'min_duration': 30},
        {'person': 'Richard', 'location': 'Fisherman\'s Wharf', 'start_avail': 870, 'end_avail': 1050, 'min_duration': 30},
        {'person': 'Robert', 'location': 'Presidio', 'start_avail': 1305, 'end_avail': 1365, 'min_duration': 60},
        {'person': 'Joseph', 'location': 'Union Square', 'start_avail': 705, 'end_avail': 885, 'min_duration': 120},
        {'person': 'Helen', 'location': 'Sunset District', 'start_avail': 885, 'end_avail': 1245, 'min_duration': 105},
        {'person': 'Elizabeth', 'location': 'Financial District', 'start_avail': 60, 'end_avail': 765, 'min_duration': 75},
        {'person': 'Kimberly', 'location': 'Haight-Ashbury', 'start_avail': 855, 'end_avail': 1050, 'min_duration': 105},
        {'person': 'Ashley', 'location': 'Russian Hill', 'start_avail': 690, 'end_avail': 1290, 'min_duration': 45}
    ]
    
    # Start at Marina District at 9:00 AM (time = 0 minutes)
    start_location = 'Marina District'
    start_time = 0
    
    best_count = 0
    best_schedule = []
    
    # Generate all permutations of meetings
    for perm in itertools.permutations(meetings):
        current_location = start_location
        current_time = start_time
        scheduled = []
        
        for meeting in perm:
            loc = meeting['location']
            travel_time = travel_times[current_location][loc]
            arrival_time = current_time + travel_time
            
            # Check if we can meet within the available time window
            start_meeting = max(arrival_time, meeting['start_avail'])
            end_meeting = start_meeting + meeting['min_duration']
            
            if end_meeting <= meeting['end_avail']:
                scheduled.append({
                    'person': meeting['person'],
                    'location': loc,
                    'start_time': start_meeting,
                    'end_time': end_meeting
                })
                current_time = end_meeting
                current_location = loc
        
        # Update best schedule if this permutation has more meetings
        if len(scheduled) > best_count:
            best_count = len(scheduled)
            best_schedule = scheduled
    
    # Convert best schedule to output format
    itinerary = []
    for event in best_schedule:
        # Convert minutes to time string (24-hour format)
        start_minutes = event['start_time']
        end_minutes = event['end_time']
        
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        start_str = f"{start_hour}:{start_minute:02d}"
        end_str = f"{end_hour}:{end_minute:02d}"
        
        itinerary.append({
            'action': 'meet',
            'location': event['location'],
            'person': event['person'],
            'start_time': start_str,
            'end_time': end_str
        })
    
    # Output as JSON
    output = {'itinerary': itinerary}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()