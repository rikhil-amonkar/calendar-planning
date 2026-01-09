import json
from itertools import permutations

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
    # Travel times in minutes (from -> to)
    travel_times = {
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Mission District'): 15,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Mission District'): 18,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Mission District'): 17,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Mission District'): 10,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Financial District'): 17,
        ('Mission District', 'Alamo Square'): 11
    }
    
    # Friend constraints (location, available_start, available_end, min_duration)
    friends = {
        'Helen': ('North Beach', time_to_minutes('9:00'), time_to_minutes('17:00'), 15),
        'Betty': ('Financial District', time_to_minutes('19:00'), time_to_minutes('21:45'), 90),
        'Amanda': ('Alamo Square', time_to_minutes('19:45'), time_to_minutes('21:00'), 60),
        'Kevin': ('Mission District', time_to_minutes('10:45'), time_to_minutes('14:45'), 45)
    }
    
    def can_schedule_meeting(current_time, current_location, friend, schedule):
        """Check if we can schedule a meeting with this friend given current state"""
        friend_location, available_start, available_end, min_duration = friends[friend]
        
        # Calculate travel time
        if current_location == friend_location:
            travel_time = 0
        else:
            travel_time = travel_times.get((current_location, friend_location), 999)
        
        # Earliest we can start the meeting
        earliest_start = max(current_time + travel_time, available_start)
        
        # Check if meeting fits in availability window
        if earliest_start + min_duration <= available_end:
            return earliest_start, min_duration
        return None, None
    
    def find_best_schedule():
        """Find the best schedule using backtracking with pruning"""
        best_schedule = []
        max_meetings = 0
        
        def backtrack(current_schedule, remaining_friends, current_time, current_location):
            nonlocal best_schedule, max_meetings
            
            if len(current_schedule) > max_meetings:
                best_schedule = current_schedule.copy()
                max_meetings = len(current_schedule)
            
            if not remaining_friends:
                return
            
            # Try each remaining friend
            for friend in list(remaining_friends):
                start_time, duration = can_schedule_meeting(current_time, current_location, friend, current_schedule)
                
                if start_time is not None:
                    # Schedule this friend
                    remaining_friends.remove(friend)
                    current_schedule.append({
                        'friend': friend,
                        'location': friends[friend][0],
                        'start_time': start_time,
                        'duration': duration,
                        'end_time': start_time + duration
                    })
                    
                    # Recursively try to schedule remaining friends
                    backtrack(current_schedule, remaining_friends, start_time + duration, friends[friend][0])
                    
                    # Backtrack
                    current_schedule.pop()
                    remaining_friends.add(friend)
        
        # Start from Pacific Heights at 9:00
        backtrack([], set(friends.keys()), time_to_minutes('9:00'), 'Pacific Heights')
        return best_schedule
    
    # Find the best schedule
    best_meetings = find_best_schedule()
    
    # Build itinerary
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Pacific Heights'
    
    for meeting in best_meetings:
        friend = meeting['friend']
        meeting_location = meeting['location']
        meeting_start = meeting['start_time']
        meeting_duration = meeting['duration']
        
        # Add travel segment if needed
        if current_location != meeting_location:
            travel_time = travel_times.get((current_location, meeting_location), 0)
            travel_end_time = current_time + travel_time
            
            itinerary.append({
                "action": "travel",
                "location": meeting_location,
                "person": "",
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(travel_end_time)
            })
            
            # Add waiting time if we arrive early
            if travel_end_time < meeting_start:
                itinerary.append({
                    "action": "wait",
                    "location": meeting_location,
                    "person": "",
                    "start_time": minutes_to_time(travel_end_time),
                    "end_time": minutes_to_time(meeting_start)
                })
            
            current_time = meeting_start
        else:
            # If we're already at the location but need to wait
            if current_time < meeting_start:
                itinerary.append({
                    "action": "wait",
                    "location": meeting_location,
                    "person": "",
                    "start_time": minutes_to_time(current_time),
                    "end_time": minutes_to_time(meeting_start)
                })
            current_time = meeting_start
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": meeting_location,
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_start + meeting_duration)
        })
        
        current_time = meeting_start + meeting_duration
        current_location = meeting_location
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()