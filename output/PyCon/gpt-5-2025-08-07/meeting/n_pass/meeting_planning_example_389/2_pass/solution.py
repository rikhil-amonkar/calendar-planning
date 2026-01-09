import json
from datetime import datetime, timedelta

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Bayview'): 26,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Mission District'): 13
    }
    
    # Friend availability (converted to minutes from 9:00)
    def time_to_minutes(hour, minute):
        return (hour * 60 + minute) - 540
    
    def minutes_to_time_str(minutes):
        total_minutes = 540 + minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{hours}:{mins:02d}"
    
    friend_availability = {
        'Sarah': {
            'location': 'Fisherman\'s Wharf',
            'start': time_to_minutes(14, 45),  # 2:45 PM
            'end': time_to_minutes(17, 30),    # 5:30 PM
            'min_duration': 105
        },
        'Mary': {
            'location': 'Richmond District', 
            'start': time_to_minutes(13, 0),   # 1:00 PM
            'end': time_to_minutes(19, 15),    # 7:15 PM
            'min_duration': 75
        },
        'Helen': {
            'location': 'Mission District',
            'start': time_to_minutes(21, 45),  # 9:45 PM
            'end': time_to_minutes(22, 30),    # 10:30 PM
            'min_duration': 30
        },
        'Thomas': {
            'location': 'Bayview',
            'start': time_to_minutes(15, 15),  # 3:15 PM
            'end': time_to_minutes(18, 45),    # 6:45 PM
            'min_duration': 120
        }
    }
    
    def can_schedule_meeting(current_schedule, new_friend, new_start, new_duration):
        """Check if a new meeting can be scheduled without conflicts"""
        new_end = new_start + new_duration
        new_loc = friend_availability[new_friend]['location']
        
        for scheduled_friend, scheduled_start, scheduled_duration in current_schedule:
            scheduled_end = scheduled_start + scheduled_duration
            scheduled_loc = friend_availability[scheduled_friend]['location']
            
            # Calculate travel times
            travel_to_new = travel_times.get((scheduled_loc, new_loc), 0)
            travel_from_new = travel_times.get((new_loc, scheduled_loc), 0)
            
            # Check for overlap considering travel time
            if (new_start < scheduled_end + travel_from_new and 
                new_end > scheduled_start - travel_to_new):
                return False
        
        return True
    
    def find_best_schedule(current_schedule, remaining_friends, current_time, current_location):
        """Recursive function to find the best schedule"""
        if not remaining_friends:
            return current_schedule[:]  # Return a copy of the current schedule
        
        best_schedule = current_schedule[:]
        
        for i, friend in enumerate(remaining_friends):
            info = friend_availability[friend]
            
            # Calculate earliest possible start considering travel from current location
            travel_time = travel_times.get((current_location, info['location']), 0)
            earliest_start = max(current_time + travel_time, info['start'])
            
            # Try different durations (from max possible down to min duration)
            max_possible_duration = info['end'] - earliest_start
            if max_possible_duration < info['min_duration']:
                continue  # Can't meet this friend
                
            # Try the maximum duration first (greedy approach)
            for duration in range(max_possible_duration, info['min_duration'] - 1, -5):  # Step by 5 minutes for efficiency
                if duration < info['min_duration']:
                    continue
                    
                start_time = earliest_start
                
                if can_schedule_meeting(current_schedule, friend, start_time, duration):
                    new_schedule = current_schedule + [(friend, start_time, duration)]
                    new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                    new_time = start_time + duration
                    new_location = info['location']
                    
                    # Recursively try to schedule remaining friends
                    candidate_schedule = find_best_schedule(
                        new_schedule, new_remaining, new_time, new_location
                    )
                    
                    # Keep the schedule with most meetings or longest total duration
                    if len(candidate_schedule) > len(best_schedule):
                        best_schedule = candidate_schedule
                    elif len(candidate_schedule) == len(best_schedule):
                        current_total = sum(dur for _, _, dur in best_schedule)
                        candidate_total = sum(dur for _, _, dur in candidate_schedule)
                        if candidate_total > current_total:
                            best_schedule = candidate_schedule
        
        return best_schedule
    
    # Start from Haight-Ashbury at 9:00 AM (time = 0 minutes)
    start_location = 'Haight-Ashbury'
    start_time = 0
    
    friends_list = list(friend_availability.keys())
    
    # Find the best schedule
    best_schedule = find_best_schedule([], friends_list, start_time, start_location)
    
    # Build itinerary
    itinerary = []
    current_location = start_location
    
    # Sort meetings by start time
    best_schedule.sort(key=lambda x: x[1])
    
    for friend, start, duration in best_schedule:
        info = friend_availability[friend]
        end = start + duration
        
        # Add travel time if needed
        if current_location != info['location']:
            travel_time = travel_times.get((current_location, info['location']), 0)
            # Note: Travel is implied between meetings
        
        # Add meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": info['location'],
            "person": friend,
            "start_time": minutes_to_time_str(start),
            "end_time": minutes_to_time_str(end)
        })
        
        current_location = info['location']
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()