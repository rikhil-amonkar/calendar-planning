# SOLUTION:
import itertools
import json

def main():
    # Build travel time dictionary
    travel = {
        'Bayview': {
            'Nob Hill': 20,
            'Union Square': 17,
            'Chinatown': 18,
            'The Castro': 20,
            'Presidio': 31,
            'Pacific Heights': 23,
            'Russian Hill': 23
        },
        'Nob Hill': {
            'Bayview': 19,
            'Union Square': 7,
            'Chinatown': 6,
            'The Castro': 17,
            'Presidio': 17,
            'Pacific Heights': 8,
            'Russian Hill': 5
        },
        'Union Square': {
            'Bayview': 15,
            'Nob Hill': 9,
            'Chinatown': 7,
            'The Castro': 19,
            'Presidio': 24,
            'Pacific Heights': 15,
            'Russian Hill': 13
        },
        'Chinatown': {
            'Bayview': 22,
            'Nob Hill': 8,
            'Union Square': 7,
            'The Castro': 22,
            'Presidio': 19,
            'Pacific Heights': 10,
            'Russian Hill': 7
        },
        'The Castro': {
            'Bayview': 19,
            'Nob Hill': 16,
            'Union Square': 19,
            'Chinatown': 20,
            'Presidio': 20,
            'Pacific Heights': 16,
            'Russian Hill': 18
        },
        'Presidio': {
            'Bayview': 31,
            'Nob Hill': 18,
            'Union Square': 22,
            'Chinatown': 21,
            'The Castro': 21,
            'Pacific Heights': 11,
            'Russian Hill': 14
        },
        'Pacific Heights': {
            'Bayview': 22,
            'Nob Hill': 8,
            'Union Square': 12,
            'Chinatown': 11,
            'The Castro': 16,
            'Presidio': 11,
            'Russian Hill': 7
        },
        'Russian Hill': {
            'Bayview': 23,
            'Nob Hill': 5,
            'Union Square': 11,
            'Chinatown': 9,
            'The Castro': 21,
            'Presidio': 14,
            'Pacific Heights': 7
        }
    }
    
    # Define friends with their constraints (times in minutes from 9:00 AM)
    friends = [
        {'name': 'Paul', 'location': 'Nob Hill', 'start_avail': 435, 'end_avail': 735, 'min_duration': 60},
        {'name': 'Carol', 'location': 'Union Square', 'start_avail': 540, 'end_avail': 675, 'min_duration': 120},
        {'name': 'Patricia', 'location': 'Chinatown', 'start_avail': 660, 'end_avail': 750, 'min_duration': 75},
        {'name': 'Karen', 'location': 'The Castro', 'start_avail': 480, 'end_avail': 600, 'min_duration': 45},
        {'name': 'Nancy', 'location': 'Presidio', 'start_avail': 165, 'end_avail': 780, 'min_duration': 30},
        {'name': 'Jeffrey', 'location': 'Pacific Heights', 'start_avail': 660, 'end_avail': 705, 'min_duration': 45},
        {'name': 'Matthew', 'location': 'Russian Hill', 'start_avail': 405, 'end_avail': 765, 'min_duration': 75}
    ]
    
    # Initialize variables to track the best schedule
    best_schedule = []
    best_count = -1
    
    # Generate all permutations of friends
    for perm in itertools.permutations(friends):
        current_location = 'Bayview'
        current_time = 0
        schedule = []
        
        for friend in perm:
            # Get travel time to friend's location
            travel_time = travel[current_location][friend['location']]
            arrival_time = current_time + travel_time
            start_time = max(arrival_time, friend['start_avail'])
            # Check if meeting duration fits in the friend's availability
            if start_time + friend['min_duration'] <= friend['end_avail']:
                end_time = start_time + friend['min_duration']
                schedule.append({
                    'friend': friend,
                    'start_time': start_time,
                    'end_time': end_time
                })
                current_time = end_time
                current_location = friend['location']
        
        count = len(schedule)
        if count > best_count:
            best_count = count
            best_schedule = schedule
    
    # Format the itinerary
    itinerary = []
    for meeting in best_schedule:
        friend = meeting['friend']
        # Convert time in minutes to string representation
        def format_time(minutes):
            total_minutes = minutes + 540  # 9:00 AM is 540 minutes from midnight
            hour = total_minutes // 60
            minute = total_minutes % 60
            return f"{hour}:{minute:02d}"
        
        start_str = format_time(meeting['start_time'])
        end_str = format_time(meeting['end_time'])
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": start_str,
            "end_time": end_str
        })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()