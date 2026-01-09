from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Embarcadero'): 19,
        ('Mission District', 'Financial District'): 17,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Mission District'): 20,
        ('Embarcadero', 'Financial District'): 5,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Embarcadero'): 4
    }

    # Friend constraints
    friends = {
        'Joseph': {
            'location': 'Fisherman\'s Wharf',
            'available_start': datetime.strptime('8:00', '%H:%M'),
            'available_end': datetime.strptime('17:30', '%H:%M'),
            'min_duration': 90
        },
        'Jeffrey': {
            'location': 'Bayview',
            'available_start': datetime.strptime('17:30', '%H:%M'),
            'available_end': datetime.strptime('21:30', '%H:%M'),
            'min_duration': 60
        },
        'Kevin': {
            'location': 'Mission District',
            'available_start': datetime.strptime('11:15', '%H:%M'),
            'available_end': datetime.strptime('15:15', '%H:%M'),
            'min_duration': 30
        },
        'David': {
            'location': 'Embarcadero',
            'available_start': datetime.strptime('8:15', '%H:%M'),
            'available_end': datetime.strptime('9:00', '%H:%M'),
            'min_duration': 30
        },
        'Barbara': {
            'location': 'Financial District',
            'available_start': datetime.strptime('10:30', '%H:%M'),
            'available_end': datetime.strptime('16:30', '%H:%M'),
            'min_duration': 15
        }
    }

    # Start at Golden Gate Park at 9:00
    current_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Golden Gate Park'
    
    itinerary = []
    
    # Try to schedule meetings in a greedy way
    scheduled_friends = set()
    
    # Convert all times to minutes for easier calculations
    def time_to_minutes(dt):
        return dt.hour * 60 + dt.minute
    
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return datetime(2023, 1, 1, hours, mins)
    
    # Create a list of possible meetings
    possible_meetings = []
    
    for friend, data in friends.items():
        start_min = time_to_minutes(data['available_start'])
        end_min = time_to_minutes(data['available_end'])
        duration = data['min_duration']
        
        # Generate possible start times (every 5 minutes)
        for start_time_min in range(start_min, end_min - duration + 1, 5):
            possible_meetings.append({
                'friend': friend,
                'location': data['location'],
                'start_min': start_time_min,
                'end_min': start_time_min + duration,
                'duration': duration
            })
    
    # Sort possible meetings by end time (earlier first)
    possible_meetings.sort(key=lambda x: x['end_min'])
    
    # Greedy scheduling algorithm
    scheduled = []
    current_time_min = time_to_minutes(current_time)
    
    for meeting in possible_meetings:
        # Skip if we've already scheduled this friend
        if meeting['friend'] in scheduled_friends:
            continue
            
        # Calculate travel time from current location
        travel_time = travel_times.get((current_location, meeting['location']), 0)
        
        # Check if we can make it to this meeting
        arrival_time = current_time_min + travel_time
        
        if arrival_time <= meeting['start_min']:
            # We can make it to this meeting
            scheduled.append({
                'friend': meeting['friend'],
                'location': meeting['location'],
                'travel_time': travel_time,
                'start_min': meeting['start_min'],
                'end_min': meeting['end_min'],
                'duration': meeting['duration']  # Add duration here
            })
            
            scheduled_friends.add(meeting['friend'])
            current_time_min = meeting['end_min']
            current_location = meeting['location']
    
    # Build the itinerary
    current_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Golden Gate Park'
    
    for meeting in scheduled:
        # Add travel event if needed
        if current_location != meeting['location']:
            travel_duration = meeting['travel_time']
            travel_end = current_time + timedelta(minutes=travel_duration)
            
            itinerary.append({
                'action': 'travel',
                'from': current_location,
                'to': meeting['location'],
                'start_time': current_time.strftime('%H:%M'),
                'end_time': travel_end.strftime('%H:%M'),
                'duration': travel_duration
            })
            
            current_time = travel_end
            current_location = meeting['location']
        
        # Add meeting
        meeting_start = minutes_to_time(meeting['start_min'])
        meeting_end = minutes_to_time(meeting['end_min'])
        
        # If we arrived early, wait until meeting starts
        if current_time < meeting_start:
            current_time = meeting_start
        
        itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['friend'],
            'start_time': current_time.strftime('%H:%M'),
            'end_time': meeting_end.strftime('%H:%M'),
            'duration': meeting['duration']  # Now this key exists
        })
        
        current_time = meeting_end
    
    # Output result as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()