from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    time_obj = datetime.strptime(time_str, '%H:%M')
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times dictionary (in minutes)
    travel_times = {
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'The Castro'): 26,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Chinatown'): 20,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Russian Hill'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Russian Hill'): 4,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5
    }

    # Friend constraints
    friends = [
        {'name': 'Carol', 'location': 'Haight-Ashbury', 'available_start': '21:30', 'available_end': '22:30', 'min_duration': 60},
        {'name': 'Laura', 'location': 'Fisherman\'s Wharf', 'available_start': '11:45', 'available_end': '21:30', 'min_duration': 60},
        {'name': 'Karen', 'location': 'The Castro', 'available_start': '7:15', 'available_end': '14:00', 'min_duration': 75},
        {'name': 'Elizabeth', 'location': 'Chinatown', 'available_start': '12:15', 'available_end': '21:30', 'min_duration': 75},
        {'name': 'Deborah', 'location': 'Alamo Square', 'available_start': '12:00', 'available_end': '15:00', 'min_duration': 105},
        {'name': 'Jason', 'location': 'North Beach', 'available_start': '14:45', 'available_end': '19:00', 'min_duration': 90},
        {'name': 'Steven', 'location': 'Russian Hill', 'available_start': '14:45', 'available_end': '18:30', 'min_duration': 120}
    ]

    # Convert all times to minutes
    for friend in friends:
        friend['available_start_min'] = time_to_minutes(friend['available_start'])
        friend['available_end_min'] = time_to_minutes(friend['available_end'])

    # Start at Golden Gate Park at 9:00 AM
    current_time = time_to_minutes('9:00')
    current_location = 'Golden Gate Park'
    itinerary = []
    scheduled_meetings = []

    # Sort friends by availability end time (earlier deadlines first)
    friends_sorted = sorted(friends, key=lambda x: x['available_end_min'])

    # Try to schedule meetings greedily
    for friend in friends_sorted:
        # Calculate earliest possible start time considering travel
        travel_time = travel_times.get((current_location, friend['location']), 30)
        earliest_start = current_time + travel_time
        
        # Find the best start time for this meeting
        if earliest_start < friend['available_start_min']:
            # Need to wait until friend is available
            meeting_start = friend['available_start_min']
        else:
            # Can start immediately after travel
            meeting_start = earliest_start
        
        # Check if meeting can be completed before friend's end time
        meeting_end = meeting_start + friend['min_duration']
        
        if meeting_end <= friend['available_end_min']:
            # Meeting can be scheduled
            # Add travel to itinerary
            if travel_time > 0:
                itinerary.append({
                    'action': 'travel',
                    'location': friend['location'],
                    'person': '',
                    'start_time': minutes_to_time(current_time),
                    'end_time': minutes_to_time(meeting_start)
                })
            
            # Add meeting to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            
            scheduled_meetings.append(friend['name'])
            current_time = meeting_end
            current_location = friend['location']

    # If we couldn't schedule all meetings, try a different approach
    if len(scheduled_meetings) < len(friends):
        # Reset and try scheduling by proximity
        current_time = time_to_minutes('9:00')
        current_location = 'Golden Gate Park'
        itinerary = []
        scheduled_meetings = []
        unscheduled_friends = friends.copy()
        
        while unscheduled_friends:
            # Find the closest available friend
            best_friend = None
            best_travel_time = float('inf')
            best_start_time = None
            
            for friend in unscheduled_friends:
                travel_time = travel_times.get((current_location, friend['location']), 30)
                earliest_start = current_time + travel_time
                
                # Adjust start time if needed
                if earliest_start < friend['available_start_min']:
                    meeting_start = friend['available_start_min']
                else:
                    meeting_start = earliest_start
                
                meeting_end = meeting_start + friend['min_duration']
                
                # Check if meeting is feasible
                if meeting_end <= friend['available_end_min']:
                    if travel_time < best_travel_time:
                        best_travel_time = travel_time
                        best_friend = friend
                        best_start_time = meeting_start
            
            if best_friend is None:
                # Cannot schedule any more meetings
                break
            
            # Schedule the best friend
            travel_time = travel_times.get((current_location, best_friend['location']), 30)
            
            # Add travel to itinerary
            if travel_time > 0:
                itinerary.append({
                    'action': 'travel',
                    'location': best_friend['location'],
                    'person': '',
                    'start_time': minutes_to_time(current_time),
                    'end_time': minutes_to_time(best_start_time)
                })
            
            # Add meeting to itinerary
            itinerary.append({
                'action': 'meet',
                'location': best_friend['location'],
                'person': best_friend['name'],
                'start_time': minutes_to_time(best_start_time),
                'end_time': minutes_to_time(best_start_time + best_friend['min_duration'])
            })
            
            scheduled_meetings.append(best_friend['name'])
            current_time = best_start_time + best_friend['min_duration']
            current_location = best_friend['location']
            unscheduled_friends.remove(best_friend)

    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()