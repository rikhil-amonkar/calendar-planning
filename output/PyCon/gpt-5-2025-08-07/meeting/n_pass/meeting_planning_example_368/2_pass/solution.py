from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Financial District'): 19,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Financial District'): 11,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Russian Hill'): 10,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'North Beach'): 7
    }
    
    # Friend availability windows (in minutes from 9:00 AM)
    availability = {
        'Joseph': {
            'location': 'Russian Hill',
            'start': time_to_minutes('8:30') - time_to_minutes('9:00'),  # -30 minutes
            'end': time_to_minutes('19:15') - time_to_minutes('9:00'),   # 615 minutes
            'duration': 60
        },
        'Nancy': {
            'location': 'Alamo Square', 
            'start': time_to_minutes('11:00') - time_to_minutes('9:00'),  # 120 minutes
            'end': time_to_minutes('16:00') - time_to_minutes('9:00'),    # 420 minutes
            'duration': 90
        },
        'Jason': {
            'location': 'North Beach',
            'start': time_to_minutes('16:45') - time_to_minutes('9:00'),  # 465 minutes
            'end': time_to_minutes('21:45') - time_to_minutes('9:00'),    # 765 minutes
            'duration': 15
        },
        'Jeffrey': {
            'location': 'Financial District',
            'start': time_to_minutes('10:30') - time_to_minutes('9:00'),  # 90 minutes
            'end': time_to_minutes('15:45') - time_to_minutes('9:00'),    # 405 minutes
            'duration': 45
        }
    }
    
    # Start from Bayview at 9:00 AM
    current_time = 0  # minutes from 9:00 AM
    current_location = 'Bayview'
    itinerary = []
    scheduled_friends = set()
    
    # Try to schedule meetings in a smart order
    # Sort friends by their availability window start time
    friends_sorted = sorted(availability.keys(), key=lambda f: availability[f]['start'])
    
    for friend in friends_sorted:
        if friend in scheduled_friends:
            continue
            
        friend_info = availability[friend]
        
        # Calculate travel time to this friend
        travel_time = travel_times.get((current_location, friend_info['location']), 0)
        
        # Earliest we can start this meeting
        earliest_start = max(current_time + travel_time, friend_info['start'])
        
        # Check if we can fit this meeting
        if earliest_start + friend_info['duration'] <= friend_info['end']:
            # Schedule this meeting
            start_time = earliest_start
            end_time = start_time + friend_info['duration']
            
            itinerary.append({
                "action": "meet",
                "location": friend_info['location'],
                "person": friend,
                "start_time": minutes_to_time(start_time + time_to_minutes('9:00')),
                "end_time": minutes_to_time(end_time + time_to_minutes('9:00'))
            })
            
            scheduled_friends.add(friend)
            current_time = end_time
            current_location = friend_info['location']
    
    # If we couldn't schedule all friends, try a different approach
    # Try all permutations to find the optimal order
    if len(scheduled_friends) < len(availability):
        from itertools import permutations
        
        best_itinerary = []
        max_meetings = 0
        
        # Try all possible orders of friends
        for order in permutations(availability.keys()):
            temp_itinerary = []
            temp_current_time = 0
            temp_current_location = 'Bayview'
            temp_scheduled = set()
            
            for friend in order:
                friend_info = availability[friend]
                
                travel_time = travel_times.get((temp_current_location, friend_info['location']), 0)
                earliest_start = max(temp_current_time + travel_time, friend_info['start'])
                
                if earliest_start + friend_info['duration'] <= friend_info['end']:
                    end_time = earliest_start + friend_info['duration']
                    
                    temp_itinerary.append({
                        "action": "meet",
                        "location": friend_info['location'],
                        "person": friend,
                        "start_time": minutes_to_time(earliest_start + time_to_minutes('9:00')),
                        "end_time": minutes_to_time(end_time + time_to_minutes('9:00'))
                    })
                    
                    temp_scheduled.add(friend)
                    temp_current_time = end_time
                    temp_current_location = friend_info['location']
            
            if len(temp_scheduled) > max_meetings:
                max_meetings = len(temp_scheduled)
                best_itinerary = temp_itinerary
        
        itinerary = best_itinerary
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    time_obj = datetime.strptime(time_str, '%H:%M')
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()