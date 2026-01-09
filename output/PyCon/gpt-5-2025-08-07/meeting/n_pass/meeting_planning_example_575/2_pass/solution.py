import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define locations and travel times (in minutes)
    locations = ['The Castro', 'Presidio', 'Sunset District', 'Haight-Ashbury', 
                'Mission District', 'Golden Gate Park', 'Russian Hill']
    
    travel_times = {
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Russian Hill'): 18,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Russian Hill'): 14,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Russian Hill'): 24,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Russian Hill'): 15,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Golden Gate Park'): 21
    }
    
    # Friend constraints
    friends = [
        {'name': 'Rebecca', 'location': 'Presidio', 'start': '18:15', 'end': '20:45', 'min_duration': 60},
        {'name': 'Linda', 'location': 'Sunset District', 'start': '15:30', 'end': '19:45', 'min_duration': 30},
        {'name': 'Elizabeth', 'location': 'Haight-Ashbury', 'start': '17:15', 'end': '19:30', 'min_duration': 105},
        {'name': 'William', 'location': 'Mission District', 'start': '13:15', 'end': '19:30', 'min_duration': 30},
        {'name': 'Robert', 'location': 'Golden Gate Park', 'start': '14:15', 'end': '21:30', 'min_duration': 45},
        {'name': 'Mark', 'location': 'Russian Hill', 'start': '10:00', 'end': '21:15', 'min_duration': 75}
    ]
    
    # Convert times to minutes
    for friend in friends:
        friend['start_min'] = time_to_minutes(friend['start'])
        friend['end_min'] = time_to_minutes(friend['end'])
    
    # Start from The Castro at 9:00
    current_location = 'The Castro'
    current_time = time_to_minutes('9:00')
    end_time = time_to_minutes('21:30')
    
    itinerary = []
    scheduled_friends = []
    
    # Try to schedule meetings in a greedy manner
    while current_time < end_time and len(scheduled_friends) < len(friends):
        best_friend = None
        best_start_time = None
        best_score = -1
        
        for friend in friends:
            if friend['name'] in scheduled_friends:
                continue
                
            # Calculate travel time to friend's location
            travel_time = travel_times.get((current_location, friend['location']), 
                                         travel_times.get((friend['location'], current_location), 30))
            
            # Earliest possible start time considering travel
            earliest_start = current_time + travel_time
            if earliest_start < friend['start_min']:
                earliest_start = friend['start_min']
            
            # Check if meeting is possible
            if earliest_start + friend['min_duration'] <= friend['end_min'] and earliest_start + friend['min_duration'] <= end_time:
                # Calculate score based on urgency and duration
                time_until_end = friend['end_min'] - earliest_start
                urgency = 1.0 / (time_until_end + 1)  # More urgent if less time available
                duration_score = friend['min_duration']
                score = urgency * duration_score
                
                if score > best_score:
                    best_score = score
                    best_friend = friend
                    best_start_time = earliest_start
        
        if best_friend is None:
            break
            
        # Schedule the meeting
        meeting_end = best_start_time + best_friend['min_duration']
        itinerary.append({
            'action': 'meet',
            'location': best_friend['location'],
            'person': best_friend['name'],
            'start_time': minutes_to_time(best_start_time),
            'end_time': minutes_to_time(meeting_end)
        })
        
        scheduled_friends.append(best_friend['name'])
        current_location = best_friend['location']
        current_time = meeting_end
    
    # Try to extend meeting durations if possible
    for i in range(len(itinerary)):
        meeting = itinerary[i]
        friend_name = meeting['person']
        
        # Find the friend
        friend = next(f for f in friends if f['name'] == friend_name)
        
        current_end = time_to_minutes(meeting['end_time'])
        max_possible_end = min(friend['end_min'], end_time)
        
        # If there's time before the next meeting or end of day, extend
        if i < len(itinerary) - 1:
            next_start = time_to_minutes(itinerary[i + 1]['start_time'])
            travel_time = travel_times.get((meeting['location'], itinerary[i + 1]['location']),
                                         travel_times.get((itinerary[i + 1]['location'], meeting['location']), 30))
            
            # We need to leave enough time for travel to next meeting
            available_extension = next_start - travel_time - current_end
        else:
            available_extension = max_possible_end - current_end
        
        if available_extension > 0:
            new_end = current_end + available_extension
            if new_end > max_possible_end:
                new_end = max_possible_end
            meeting['end_time'] = minutes_to_time(new_end)
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()