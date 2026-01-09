from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Union Square'): 17,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Union Square'): 7,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Union Square'): 22,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Union Square'): 17,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Haight-Ashbury'): 18
    }
    
    # Convert times to minutes since 9:00 AM
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, '%I:%M%p')
        base_time = datetime.strptime('9:00AM', '%I:%M%p')
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)
    
    # Convert minutes since 9:00 AM back to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime('9:00AM', '%I:%M%p')
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime('%I:%M%p').lstrip('0').lower()
    
    # Friend constraints
    friends = {
        'Barbara': {
            'location': 'North Beach',
            'available_start': time_to_minutes('1:45PM'),
            'available_end': time_to_minutes('8:15PM'),
            'min_duration': 60
        },
        'Margaret': {
            'location': 'Presidio',
            'available_start': time_to_minutes('10:15AM'),
            'available_end': time_to_minutes('3:15PM'),
            'min_duration': 30
        },
        'Kevin': {
            'location': 'Haight-Ashbury',
            'available_start': time_to_minutes('8:00PM'),
            'available_end': time_to_minutes('8:45PM'),
            'min_duration': 30
        },
        'Kimberly': {
            'location': 'Union Square',
            'available_start': time_to_minutes('7:45AM'),
            'available_end': time_to_minutes('4:45PM'),
            'min_duration': 30
        }
    }
    
    def can_schedule_meeting(current_schedule, new_friend, new_start_time):
        """Check if we can schedule a meeting with the given friend at the given time"""
        friend_info = friends[new_friend]
        new_end_time = new_start_time + friend_info['min_duration']
        
        # Check if meeting fits within friend's availability
        if new_start_time < friend_info['available_start'] or new_end_time > friend_info['available_end']:
            return False
        
        # If no meetings scheduled yet, it's valid
        if not current_schedule:
            return True
        
        # Check against all existing meetings
        for scheduled_friend, scheduled_start, scheduled_duration in current_schedule:
            scheduled_end = scheduled_start + scheduled_duration
            scheduled_location = friends[scheduled_friend]['location']
            new_location = friend_info['location']
            
            # Check if new meeting overlaps with scheduled meeting
            if not (new_end_time <= scheduled_start or new_start_time >= scheduled_end):
                return False
            
            # Check travel time constraints
            if new_start_time > scheduled_end:
                # New meeting after scheduled meeting
                travel_time = travel_times.get((scheduled_location, new_location), 999)
                if scheduled_end + travel_time > new_start_time:
                    return False
            elif scheduled_start > new_end_time:
                # Scheduled meeting after new meeting
                travel_time = travel_times.get((new_location, scheduled_location), 999)
                if new_end_time + travel_time > scheduled_start:
                    return False
        
        return True
    
    def find_best_schedule():
        """Find the best schedule using a greedy approach with backtracking"""
        friend_names = list(friends.keys())
        best_schedule = []
        max_meetings = 0
        
        def backtrack(current_schedule, remaining_friends):
            nonlocal best_schedule, max_meetings
            
            if len(current_schedule) > max_meetings:
                best_schedule = current_schedule.copy()
                max_meetings = len(current_schedule)
            
            if not remaining_friends:
                return
            
            # Try to schedule each remaining friend
            for i, friend in enumerate(remaining_friends):
                friend_info = friends[friend]
                
                # Try different start times within the friend's availability window
                earliest_start = friend_info['available_start']
                latest_start = friend_info['available_end'] - friend_info['min_duration']
                
                # Sample reasonable start times instead of trying every minute
                time_slots = []
                if latest_start - earliest_start > 120:  # More than 2 hours window
                    # Sample every 30 minutes
                    for t in range(earliest_start, latest_start + 1, 30):
                        time_slots.append(t)
                else:
                    # Sample every 15 minutes
                    for t in range(earliest_start, latest_start + 1, 15):
                        time_slots.append(t)
                
                # Always include the boundaries
                if earliest_start not in time_slots:
                    time_slots.insert(0, earliest_start)
                if latest_start not in time_slots:
                    time_slots.append(latest_start)
                
                for start_time in time_slots:
                    if can_schedule_meeting(current_schedule, friend, start_time):
                        new_schedule = current_schedule + [(friend, start_time, friend_info['min_duration'])]
                        new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                        backtrack(new_schedule, new_remaining)
        
        # Start with empty schedule and all friends
        backtrack([], friend_names)
        return best_schedule
    
    # Find the best schedule
    best_schedule = find_best_schedule()
    
    # Build itinerary
    itinerary = []
    
    if best_schedule:
        # Sort meetings by start time
        best_schedule.sort(key=lambda x: x[1])
        
        current_location = 'Bayview'
        
        for friend, start_time, duration in best_schedule:
            location = friends[friend]['location']
            
            # Add travel from current location if needed
            if current_location != location:
                travel_time = travel_times.get((current_location, location), 0)
                # Note: We don't add travel as a separate action, but account for it in timing
            
            # Add meeting
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(start_time + duration)
            })
            
            current_location = location
    
    # Output result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()