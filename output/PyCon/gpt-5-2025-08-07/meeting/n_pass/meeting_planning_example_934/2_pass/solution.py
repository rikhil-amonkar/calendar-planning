import json
from datetime import datetime, timedelta

def main():
    # Travel times dictionary
    travel_times = {
        'Nob Hill': {
            'Embarcadero': 9, 'The Castro': 17, 'Haight-Ashbury': 13, 'Union Square': 7,
            'North Beach': 8, 'Pacific Heights': 8, 'Chinatown': 6, 'Golden Gate Park': 17,
            'Marina District': 11, 'Russian Hill': 5
        },
        'Embarcadero': {
            'Nob Hill': 10, 'The Castro': 25, 'Haight-Ashbury': 21, 'Union Square': 10,
            'North Beach': 5, 'Pacific Heights': 11, 'Chinatown': 7, 'Golden Gate Park': 25,
            'Marina District': 12, 'Russian Hill': 8
        },
        'The Castro': {
            'Nob Hill': 16, 'Embarcadero': 22, 'Haight-Ashbury': 6, 'Union Square': 19,
            'North Beach': 20, 'Pacific Heights': 16, 'Chinatown': 22, 'Golden Gate Park': 11,
            'Marina District': 21, 'Russian Hill': 18
        },
        'Haight-Ashbury': {
            'Nob Hill': 15, 'Embarcadero': 20, 'The Castro': 6, 'Union Square': 19,
            'North Beach': 19, 'Pacific Heights': 12, 'Chinatown': 19, 'Golden Gate Park': 7,
            'Marina District': 17, 'Russian Hill': 17
        },
        'Union Square': {
            'Nob Hill': 9, 'Embarcadero': 11, 'The Castro': 17, 'Haight-Ashbury': 18,
            'North Beach': 10, 'Pacific Heights': 15, 'Chinatown': 7, 'Golden Gate Park': 22,
            'Marina District': 18, 'Russian Hill': 13
        },
        'North Beach': {
            'Nob Hill': 7, 'Embarcadero': 6, 'The Castro': 23, 'Haight-Ashbury': 18,
            'Union Square': 7, 'Pacific Heights': 8, 'Chinatown': 6, 'Golden Gate Park': 22,
            'Marina District': 9, 'Russian Hill': 4
        },
        'Pacific Heights': {
            'Nob Hill': 8, 'Embarcadero': 10, 'The Castro': 16, 'Haight-Ashbury': 11,
            'Union Square': 12, 'North Beach': 9, 'Chinatown': 11, 'Golden Gate Park': 15,
            'Marina District': 6, 'Russian Hill': 7
        },
        'Chinatown': {
            'Nob Hill': 9, 'Embarcadero': 5, 'The Castro': 22, 'Haight-Ashbury': 19,
            'Union Square': 7, 'North Beach': 3, 'Pacific Heights': 10, 'Golden Gate Park': 23,
            'Marina District': 12, 'Russian Hill': 7
        },
        'Golden Gate Park': {
            'Nob Hill': 20, 'Embarcadero': 25, 'The Castro': 13, 'Haight-Ashbury': 7,
            'Union Square': 22, 'North Beach': 23, 'Pacific Heights': 16, 'Chinatown': 23,
            'Marina District': 16, 'Russian Hill': 19
        },
        'Marina District': {
            'Nob Hill': 12, 'Embarcadero': 14, 'The Castro': 22, 'Haight-Ashbury': 16,
            'Union Square': 16, 'North Beach': 11, 'Pacific Heights': 7, 'Chinatown': 15,
            'Golden Gate Park': 18, 'Russian Hill': 8
        },
        'Russian Hill': {
            'Nob Hill': 5, 'Embarcadero': 8, 'The Castro': 21, 'Haight-Ashbury': 17,
            'Union Square': 10, 'North Beach': 5, 'Pacific Heights': 7, 'Chinatown': 9,
            'Golden Gate Park': 21, 'Marina District': 7
        }
    }

    # Friend constraints
    friends = {
        'Mary': {
            'location': 'Embarcadero',
            'available_start': datetime.strptime('20:00', '%H:%M'),
            'available_end': datetime.strptime('21:15', '%H:%M'),
            'min_duration': 75
        },
        'Kenneth': {
            'location': 'The Castro',
            'available_start': datetime.strptime('11:15', '%H:%M'),
            'available_end': datetime.strptime('19:15', '%H:%M'),
            'min_duration': 30
        },
        'Joseph': {
            'location': 'Haight-Ashbury',
            'available_start': datetime.strptime('20:00', '%H:%M'),
            'available_end': datetime.strptime('22:00', '%H:%M'),
            'min_duration': 120
        },
        'Sarah': {
            'location': 'Union Square',
            'available_start': datetime.strptime('11:45', '%H:%M'),
            'available_end': datetime.strptime('14:30', '%H:%M'),
            'min_duration': 90
        },
        'Thomas': {
            'location': 'North Beach',
            'available_start': datetime.strptime('19:15', '%H:%M'),
            'available_end': datetime.strptime('19:45', '%H:%M'),
            'min_duration': 15
        },
        'Daniel': {
            'location': 'Pacific Heights',
            'available_start': datetime.strptime('13:45', '%H:%M'),
            'available_end': datetime.strptime('20:30', '%H:%M'),
            'min_duration': 15
        },
        'Richard': {
            'location': 'Chinatown',
            'available_start': datetime.strptime('8:00', '%H:%M'),
            'available_end': datetime.strptime('18:45', '%H:%M'),
            'min_duration': 30
        },
        'Mark': {
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('17:30', '%H:%M'),
            'available_end': datetime.strptime('21:30', '%H:%M'),
            'min_duration': 120
        },
        'David': {
            'location': 'Marina District',
            'available_start': datetime.strptime('20:00', '%H:%M'),
            'available_end': datetime.strptime('21:00', '%H:%M'),
            'min_duration': 60
        },
        'Karen': {
            'location': 'Russian Hill',
            'available_start': datetime.strptime('13:15', '%H:%M'),
            'available_end': datetime.strptime('18:30', '%H:%M'),
            'min_duration': 120
        }
    }

    # Convert all times to minutes since midnight for easier calculation
    def time_to_minutes(time_obj):
        return time_obj.hour * 60 + time_obj.minute

    for friend in friends:
        friends[friend]['start_min'] = time_to_minutes(friends[friend]['available_start'])
        friends[friend]['end_min'] = time_to_minutes(friends[friend]['available_end'])

    # Greedy scheduling algorithm
    def can_schedule(current_schedule, new_friend, new_start_time):
        """Check if we can schedule a new meeting given current schedule"""
        new_end_time = new_start_time + friends[new_friend]['min_duration']
        
        # Check availability
        if new_start_time < friends[new_friend]['start_min'] or new_end_time > friends[new_friend]['end_min']:
            return False
        
        # Check conflicts with existing meetings
        for scheduled_friend, scheduled_start in current_schedule:
            scheduled_end = scheduled_start + friends[scheduled_friend]['min_duration']
            scheduled_loc = friends[scheduled_friend]['location']
            new_loc = friends[new_friend]['location']
            
            # Check if meetings overlap in time
            if not (new_end_time <= scheduled_start or new_start_time >= scheduled_end):
                return False
            
            # Check travel time constraints
            if new_start_time < scheduled_end:
                # New meeting starts after existing meeting
                travel_needed = travel_times[scheduled_loc][new_loc]
                if scheduled_end + travel_needed > new_start_time:
                    return False
            else:
                # Existing meeting starts after new meeting
                travel_needed = travel_times[new_loc][scheduled_loc]
                if new_end_time + travel_needed > scheduled_start:
                    return False
        
        return True

    # Try different orders to maximize number of meetings
    best_schedule = []
    friend_names = list(friends.keys())
    
    # Try scheduling by earliest end time first
    sorted_friends = sorted(friend_names, key=lambda x: friends[x]['end_min'])
    
    current_schedule = []
    for friend in sorted_friends:
        # Try to schedule at the earliest possible time
        earliest_start = friends[friend]['start_min']
        
        # If we have previous meetings, find the earliest start considering travel
        if current_schedule:
            last_friend, last_start = current_schedule[-1]
            last_end = last_start + friends[last_friend]['min_duration']
            last_loc = friends[last_friend]['location']
            current_loc = friends[friend]['location']
            
            travel_time = travel_times[last_loc][current_loc]
            earliest_after_travel = last_end + travel_time
            earliest_start = max(earliest_start, earliest_after_travel)
        
        # Check if we can schedule at earliest_start
        if can_schedule(current_schedule, friend, earliest_start):
            current_schedule.append((friend, earliest_start))
    
    best_schedule = current_schedule
    
    # Convert schedule to itinerary format
    itinerary = []
    for friend, start_min in best_schedule:
        duration = friends[friend]['min_duration']
        location = friends[friend]['location']
        
        start_time = datetime(2023, 1, 1, start_min // 60, start_min % 60)
        end_time = start_time + timedelta(minutes=duration)
        
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": friend,
            "start_time": start_time.strftime('%H:%M').lstrip('0').replace(':0', ':'),
            "end_time": end_time.strftime('%H:%M').lstrip('0').replace(':0', ':')
        })
    
    # Sort by start time
    itinerary.sort(key=lambda x: datetime.strptime(x['start_time'], '%H:%M'))
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()