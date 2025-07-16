import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Travel times between locations in minutes
travel_times = {
    'Russian Hill': {
        'Russian Hill': 0,
        'Financial District': 15,
        'Mission District': 20,
        'Berkeley': 30,
        'North Beach': 10
    },
    'Financial District': {
        'Russian Hill': 15,
        'Financial District': 0,
        'Mission District': 10,
        'Berkeley': 25,
        'North Beach': 15
    },
    'Mission District': {
        'Russian Hill': 20,
        'Financial District': 10,
        'Mission District': 0,
        'Berkeley': 20,
        'North Beach': 25
    },
    'Berkeley': {
        'Russian Hill': 30,
        'Financial District': 25,
        'Mission District': 20,
        'Berkeley': 0,
        'North Beach': 35
    },
    'North Beach': {
        'Russian Hill': 10,
        'Financial District': 15,
        'Mission District': 25,
        'Berkeley': 35,
        'North Beach': 0
    }
}

# Friends data with their availability
friends = {
    'Alice': {
        'location': 'Financial District',
        'start': '10:00',
        'end': '12:00',
        'duration': 30
    },
    'Bob': {
        'location': 'Mission District',
        'start': '11:00',
        'end': '13:00',
        'duration': 45
    },
    'Charlie': {
        'location': 'Berkeley',
        'start': '12:00',
        'end': '15:00',
        'duration': 60
    },
    'Dana': {
        'location': 'North Beach',
        'start': '09:30',
        'end': '11:30',
        'duration': 30
    }
}

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc]

def generate_itinerary():
    itinerary = []
    current_time = time_to_minutes('09:00')
    current_location = 'Russian Hill'
    
    # Create a list of friends to visit
    friends_to_visit = list(friends.keys())
    visited = set()
    
    while len(visited) < len(friends_to_visit):
        best_friend = None
        best_start = None
        earliest_end = float('inf')
        
        for name in friends_to_visit:
            if name in visited:
                continue
                
            friend = friends[name]
            location = friend['location']
            travel_time = get_travel_time(current_location, location)
            arrival_time = current_time + travel_time
            
            # Calculate possible meeting window
            window_start = max(arrival_time, time_to_minutes(friend['start']))
            window_end = window_start + friend['duration']
            
            # Check if we can complete the full duration before friend's end time
            if window_end <= time_to_minutes(friend['end']):
                # Prioritize friends with earlier end times
                if time_to_minutes(friend['end']) < earliest_end:
                    best_friend = name
                    best_start = window_start
                    earliest_end = time_to_minutes(friend['end'])
        
        if best_friend is None:
            break  # No more valid visits possible
            
        # Add to itinerary
        friend_data = friends[best_friend]
        end_time = best_start + friend_data['duration']
        
        itinerary.append({
            'action': 'meet',
            'location': friend_data['location'],
            'person': best_friend,
            'start_time': minutes_to_time(best_start),
            'end_time': minutes_to_time(end_time)
        })
        
        visited.add(best_friend)
        current_location = friend_data['location']
        current_time = end_time
    
    return itinerary

def main():
    itinerary = generate_itinerary()
    print(json.dumps({'itinerary': itinerary}, indent=2))

if __name__ == '__main__':
    main()