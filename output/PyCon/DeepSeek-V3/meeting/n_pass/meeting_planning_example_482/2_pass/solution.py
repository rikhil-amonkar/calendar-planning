import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric matrix)
    travel_times = {
        'Haight-Ashbury': {
            'Mission District': 11,
            'Bayview': 18,
            'Pacific Heights': 12,
            'Russian Hill': 17,
            'Fisherman\'s Wharf': 23
        },
        'Mission District': {
            'Haight-Ashbury': 12,
            'Bayview': 15,
            'Pacific Heights': 16,
            'Russian Hill': 15,
            'Fisherman\'s Wharf': 22
        },
        'Bayview': {
            'Haight-Ashbury': 19,
            'Mission District': 13,
            'Pacific Heights': 23,
            'Russian Hill': 23,
            'Fisherman\'s Wharf': 25
        },
        'Pacific Heights': {
            'Haight-Ashbury': 11,
            'Mission District': 15,
            'Bayview': 22,
            'Russian Hill': 7,
            'Fisherman\'s Wharf': 13
        },
        'Russian Hill': {
            'Haight-Ashbury': 17,
            'Mission District': 16,
            'Bayview': 23,
            'Pacific Heights': 7,
            'Fisherman\'s Wharf': 7
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22,
            'Mission District': 22,
            'Bayview': 26,
            'Pacific Heights': 12,
            'Russian Hill': 7
        }
    }
    
    # Friend constraints
    friends = {
        'Stephanie': {
            'location': 'Mission District',
            'available_start': '8:15',
            'available_end': '13:45',
            'min_duration': 90
        },
        'Sandra': {
            'location': 'Bayview',
            'available_start': '13:00',
            'available_end': '19:30',
            'min_duration': 15
        },
        'Richard': {
            'location': 'Pacific Heights',
            'available_start': '7:15',
            'available_end': '10:15',
            'min_duration': 75
        },
        'Brian': {
            'location': 'Russian Hill',
            'available_start': '12:15',
            'available_end': '16:00',
            'min_duration': 120
        },
        'Jason': {
            'location': 'Fisherman\'s Wharf',
            'available_start': '8:30',
            'available_end': '17:45',
            'min_duration': 60
        }
    }
    
    # Convert all times to minutes
    for friend in friends.values():
        friend['available_start_min'] = time_to_minutes(friend['available_start'])
        friend['available_end_min'] = time_to_minutes(friend['available_end'])
    
    start_location = 'Haight-Ashbury'
    current_time = time_to_minutes('9:00')
    
    def can_schedule_meeting(current_loc, current_time_val, friend_name, schedule):
        """Check if we can schedule a meeting with this friend given current schedule"""
        friend_info = friends[friend_name]
        location = friend_info['location']
        
        # Calculate travel time
        travel_time = travel_times[current_loc][location]
        
        # Earliest we can arrive
        arrival_time = current_time_val + travel_time
        
        # Check if we can arrive within friend's availability
        if arrival_time > friend_info['available_end_min']:
            return None, None
        
        # Calculate meeting start time (can't start before friend's availability)
        meeting_start = max(arrival_time, friend_info['available_start_min'])
        
        # Check if we have enough time for minimum duration
        if meeting_start + friend_info['min_duration'] > friend_info['available_end_min']:
            return None, None
        
        # Try to schedule the full minimum duration
        meeting_end = meeting_start + friend_info['min_duration']
        
        return meeting_start, meeting_end
    
    def find_best_schedule(current_schedule, current_loc, current_time_val, remaining_friends, best_schedule):
        """Recursive function to find the best schedule"""
        if not remaining_friends:
            # No more friends to schedule, check if this is better than current best
            if len(current_schedule) > len(best_schedule['schedule']):
                best_schedule['schedule'] = current_schedule.copy()
            elif len(current_schedule) == len(best_schedule['schedule']):
                # Same number of meetings, compare total duration
                current_duration = sum(meeting['duration'] for meeting in current_schedule)
                best_duration = sum(meeting['duration'] for meeting in best_schedule['schedule'])
                if current_duration > best_duration:
                    best_schedule['schedule'] = current_schedule.copy()
            return
        
        # Try to schedule each remaining friend
        for i, friend_name in enumerate(remaining_friends):
            meeting_start, meeting_end = can_schedule_meeting(current_loc, current_time_val, friend_name, current_schedule)
            
            if meeting_start is not None:
                # Can schedule this friend
                new_schedule = current_schedule + [{
                    'friend': friend_name,
                    'location': friends[friend_name]['location'],
                    'start': meeting_start,
                    'end': meeting_end,
                    'duration': meeting_end - meeting_start
                }]
                
                new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                
                # Continue with next friend from this location and time
                find_best_schedule(new_schedule, friends[friend_name]['location'], meeting_end, new_remaining, best_schedule)
        
        # Also try not scheduling any more friends (this path might be better)
        if len(current_schedule) > len(best_schedule['schedule']):
            best_schedule['schedule'] = current_schedule.copy()
        elif len(current_schedule) == len(best_schedule['schedule']):
            current_duration = sum(meeting['duration'] for meeting in current_schedule)
            best_duration = sum(meeting['duration'] for meeting in best_schedule['schedule'])
            if current_duration > best_duration:
                best_schedule['schedule'] = current_schedule.copy()
    
    # Find the best schedule
    all_friends = list(friends.keys())
    best_schedule = {'schedule': []}
    
    find_best_schedule([], start_location, current_time, all_friends, best_schedule)
    
    # Build itinerary
    itinerary = []
    current_loc = start_location
    current_time_val = current_time
    
    for i, meeting in enumerate(best_schedule['schedule']):
        # Add travel to meeting location
        travel_time = travel_times[current_loc][meeting['location']]
        travel_start = current_time_val
        travel_end = current_time_val + travel_time
        
        itinerary.append({
            "action": "travel",
            "location": meeting['location'],
            "person": "",
            "start_time": minutes_to_time(travel_start),
            "end_time": minutes_to_time(travel_end)
        })
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['friend'],
            "start_time": minutes_to_time(meeting['start']),
            "end_time": minutes_to_time(meeting['end'])
        })
        
        # Update current location and time
        current_loc = meeting['location']
        current_time_val = meeting['end']
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()