import json
from datetime import datetime, timedelta

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Mission District': {
            'Mission District': 0, 'The Castro': 7, 'Nob Hill': 12, 'Presidio': 25,
            'Marina District': 19, 'Pacific Heights': 16, 'Golden Gate Park': 17,
            'Chinatown': 16, 'Richmond District': 20
        },
        'The Castro': {
            'Mission District': 7, 'The Castro': 0, 'Nob Hill': 16, 'Presidio': 20,
            'Marina District': 21, 'Pacific Heights': 16, 'Golden Gate Park': 11,
            'Chinatown': 22, 'Richmond District': 16
        },
        'Nob Hill': {
            'Mission District': 13, 'The Castro': 17, 'Nob Hill': 0, 'Presidio': 17,
            'Marina District': 11, 'Pacific Heights': 8, 'Golden Gate Park': 17,
            'Chinatown': 6, 'Richmond District': 14
        },
        'Presidio': {
            'Mission District': 26, 'The Castro': 21, 'Nob Hill': 18, 'Presidio': 0,
            'Marina District': 11, 'Pacific Heights': 11, 'Golden Gate Park': 12,
            'Chinatown': 21, 'Richmond District': 7
        },
        'Marina District': {
            'Mission District': 20, 'The Castro': 22, 'Nob Hill': 12, 'Presidio': 10,
            'Marina District': 0, 'Pacific Heights': 7, 'Golden Gate Park': 18,
            'Chinatown': 15, 'Richmond District': 11
        },
        'Pacific Heights': {
            'Mission District': 15, 'The Castro': 16, 'Nob Hill': 8, 'Presidio': 11,
            'Marina District': 6, 'Pacific Heights': 0, 'Golden Gate Park': 15,
            'Chinatown': 11, 'Richmond District': 12
        },
        'Golden Gate Park': {
            'Mission District': 17, 'The Castro': 13, 'Nob Hill': 20, 'Presidio': 11,
            'Marina District': 16, 'Pacific Heights': 16, 'Golden Gate Park': 0,
            'Chinatown': 23, 'Richmond District': 7
        },
        'Chinatown': {
            'Mission District': 17, 'The Castro': 22, 'Nob Hill': 9, 'Presidio': 19,
            'Marina District': 12, 'Pacific Heights': 10, 'Golden Gate Park': 23,
            'Chinatown': 0, 'Richmond District': 20
        },
        'Richmond District': {
            'Mission District': 20, 'The Castro': 16, 'Nob Hill': 17, 'Presidio': 7,
            'Marina District': 9, 'Pacific Heights': 10, 'Golden Gate Park': 9,
            'Chinatown': 20, 'Richmond District': 0
        }
    }

    # Define friends' availability and constraints
    friends = {
        'Lisa': {
            'location': 'The Castro',
            'available_start': datetime.strptime('19:15', '%H:%M'),
            'available_end': datetime.strptime('21:15', '%H:%M'),
            'min_duration': 120
        },
        'Daniel': {
            'location': 'Nob Hill',
            'available_start': datetime.strptime('8:15', '%H:%M'),
            'available_end': datetime.strptime('11:00', '%H:%M'),
            'min_duration': 15
        },
        'Elizabeth': {
            'location': 'Presidio',
            'available_start': datetime.strptime('21:15', '%H:%M'),
            'available_end': datetime.strptime('22:15', '%H:%M'),
            'min_duration': 45
        },
        'Steven': {
            'location': 'Marina District',
            'available_start': datetime.strptime('16:30', '%H:%M'),
            'available_end': datetime.strptime('20:45', '%H:%M'),
            'min_duration': 90
        },
        'Timothy': {
            'location': 'Pacific Heights',
            'available_start': datetime.strptime('12:00', '%H:%M'),
            'available_end': datetime.strptime('18:00', '%H:%M'),
            'min_duration': 90
        },
        'Ashley': {
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('20:45', '%H:%M'),
            'available_end': datetime.strptime('21:45', '%H:%M'),
            'min_duration': 60
        },
        'Kevin': {
            'location': 'Chinatown',
            'available_start': datetime.strptime('12:00', '%H:%M'),
            'available_end': datetime.strptime('19:00', '%H:%M'),
            'min_duration': 30
        },
        'Betty': {
            'location': 'Richmond District',
            'available_start': datetime.strptime('13:15', '%H:%M'),
            'available_end': datetime.strptime('15:45', '%H:%M'),
            'min_duration': 30
        }
    }

    def can_schedule_meeting(current_time, current_location, friend_name, itinerary):
        friend = friends[friend_name]
        
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        # Check if we can arrive before their availability ends
        if arrival_time >= friend['available_end']:
            return None, None
        
        # Determine start time (max of arrival time and friend's available start)
        start_time = max(arrival_time, friend['available_start'])
        
        # Check if we have enough time for minimum duration
        end_time = start_time + timedelta(minutes=friend['min_duration'])
        if end_time > friend['available_end']:
            return None, None
        
        return start_time, end_time

    # Start from Mission District at 9:00
    current_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Mission District'
    itinerary = []
    met_friends = set()

    # Try to meet friends in a priority order that maximizes the number of meetings
    # We'll use a greedy approach, trying to schedule friends with earlier availability first
    
    # Sort friends by available start time
    sorted_friends = sorted(friends.keys(), key=lambda f: friends[f]['available_start'])
    
    for friend in sorted_friends:
        if friend in met_friends:
            continue
            
        start_time, end_time = can_schedule_meeting(current_time, current_location, friend, itinerary)
        
        if start_time and end_time:
            # Add travel action if needed
            if current_location != friends[friend]['location']:
                travel_duration = travel_times[current_location][friends[friend]['location']]
                travel_end = current_time + timedelta(minutes=travel_duration)
                
                # Only add travel action if we're actually moving
                if current_location != friends[friend]['location']:
                    itinerary.append({
                        "action": "travel",
                        "from": current_location,
                        "to": friends[friend]['location'],
                        "start_time": current_time.strftime('%H:%M'),
                        "end_time": travel_end.strftime('%H:%M')
                    })
            
            # Add meeting
            itinerary.append({
                "action": "meet",
                "location": friends[friend]['location'],
                "person": friend,
                "start_time": start_time.strftime('%H:%M'),
                "end_time": end_time.strftime('%H:%M')
            })
            
            met_friends.add(friend)
            current_time = end_time
            current_location = friends[friend]['location']

    # Try to fill gaps with additional friends we might have missed
    # This is a second pass to catch friends we might have skipped due to ordering
    remaining_friends = [f for f in friends.keys() if f not in met_friends]
    
    for friend in remaining_friends:
        start_time, end_time = can_schedule_meeting(current_time, current_location, friend, itinerary)
        
        if start_time and end_time:
            # Add travel action if needed
            if current_location != friends[friend]['location']:
                travel_duration = travel_times[current_location][friends[friend]['location']]
                travel_end = current_time + timedelta(minutes=travel_duration)
                
                itinerary.append({
                    "action": "travel",
                    "from": current_location,
                    "to": friends[friend]['location'],
                    "start_time": current_time.strftime('%H:%M'),
                    "end_time": travel_end.strftime('%H:%M')
                })
            
            # Add meeting
            itinerary.append({
                "action": "meet",
                "location": friends[friend]['location'],
                "person": friend,
                "start_time": start_time.strftime('%H:%M'),
                "end_time": end_time.strftime('%H:%M')
            })
            
            met_friends.add(friend)
            current_time = end_time
            current_location = friends[friend]['location']

    # Final optimization: try to meet Elizabeth if we finish early enough
    if 'Elizabeth' not in met_friends:
        start_time, end_time = can_schedule_meeting(current_time, current_location, 'Elizabeth', itinerary)
        if start_time and end_time:
            # Add travel action if needed
            if current_location != friends['Elizabeth']['location']:
                travel_duration = travel_times[current_location][friends['Elizabeth']['location']]
                travel_end = current_time + timedelta(minutes=travel_duration)
                
                itinerary.append({
                    "action": "travel",
                    "from": current_location,
                    "to": friends['Elizabeth']['location'],
                    "start_time": current_time.strftime('%H:%M'),
                    "end_time": travel_end.strftime('%H:%M')
                })
            
            # Add meeting
            itinerary.append({
                "action": "meet",
                "location": friends['Elizabeth']['location'],
                "person": 'Elizabeth',
                "start_time": start_time.strftime('%H:%M'),
                "end_time": end_time.strftime('%H:%M')
            })

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()