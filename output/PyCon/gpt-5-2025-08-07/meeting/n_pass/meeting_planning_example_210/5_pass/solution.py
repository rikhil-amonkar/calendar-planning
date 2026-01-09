from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21
    }
    
    # Friend constraints
    friends = {
        'Emily': {
            'location': 'Presidio',
            'available_start': datetime.strptime('16:15', '%H:%M'),
            'available_end': datetime.strptime('21:00', '%H:%M'),
            'min_duration': 105
        },
        'Joseph': {
            'location': 'Richmond District',
            'available_start': datetime.strptime('17:15', '%H:%M'),
            'available_end': datetime.strptime('22:00', '%H:%M'),
            'min_duration': 120
        },
        'Melissa': {
            'location': 'Financial District',
            'available_start': datetime.strptime('15:45', '%H:%M'),
            'available_end': datetime.strptime('21:45', '%H:%M'),
            'min_duration': 75
        }
    }
    
    start_location = 'Fisherman\'s Wharf'
    start_time = datetime.strptime('09:00', '%H:%M')
    
    def find_best_schedule():
        best_schedule = None
        max_total_duration = 0
        
        # Try all possible orders (only 6 permutations for 3 friends)
        from itertools import permutations
        friend_names = list(friends.keys())
        
        for order in permutations(friend_names):
            # Try to schedule meetings in this order
            schedule = []
            current_time = start_time
            current_location = start_location
            total_duration = 0
            valid_schedule = True
            
            for friend in order:
                friend_info = friends[friend]
                
                # Calculate travel time to this friend
                travel_time = travel_times.get((current_location, friend_info['location']), 0)
                
                # Earliest we can start this meeting
                earliest_start = current_time + timedelta(minutes=travel_time)
                
                # If we arrive before friend's availability, wait until they're available
                if earliest_start < friend_info['available_start']:
                    meeting_start = friend_info['available_start']
                else:
                    meeting_start = earliest_start
                
                # Check if we can have the minimum duration
                meeting_end = meeting_start + timedelta(minutes=friend_info['min_duration'])
                
                if meeting_end > friend_info['available_end']:
                    valid_schedule = False
                    break
                
                # Try to maximize duration within friend's availability
                max_possible_end = friend_info['available_end']
                max_duration = int((max_possible_end - meeting_start).total_seconds() / 60)
                
                # Use maximum possible duration
                actual_duration = max_duration
                actual_end = meeting_start + timedelta(minutes=actual_duration)
                
                schedule.append({
                    'person': friend,
                    'location': friend_info['location'],
                    'start_time': meeting_start,
                    'end_time': actual_end,
                    'duration': actual_duration
                })
                
                total_duration += actual_duration
                current_time = actual_end
                current_location = friend_info['location']
            
            if valid_schedule and total_duration > max_total_duration:
                max_total_duration = total_duration
                best_schedule = schedule
        
        return best_schedule
    
    def optimize_schedule_durations(schedule):
        """Optimize durations to maximize total time while respecting constraints"""
        if not schedule:
            return schedule
        
        # Work backwards to maximize durations
        for i in range(len(schedule)-1, -1, -1):
            current_meeting = schedule[i]
            friend = friends[current_meeting['person']]
            
            # Maximum possible end time is friend's availability end
            max_end_time = friend['available_end']
            
            # If this is not the last meeting, we're constrained by the next meeting's start time
            if i < len(schedule) - 1:
                next_meeting = schedule[i+1]
                travel_time = travel_times.get(
                    (current_meeting['location'], next_meeting['location']), 0
                )
                # Latest we can end this meeting to make it to the next one on time
                max_end_time = min(max_end_time, 
                                 next_meeting['start_time'] - timedelta(minutes=travel_time))
            
            # Calculate maximum possible duration
            max_duration = int((max_end_time - current_meeting['start_time']).total_seconds() / 60)
            
            # Update with maximum duration
            current_meeting['end_time'] = current_meeting['start_time'] + timedelta(minutes=max_duration)
            current_meeting['duration'] = max_duration
        
        return schedule
    
    # Find initial schedule
    best_schedule = find_best_schedule()
    
    if best_schedule:
        # Optimize durations
        optimized_schedule = optimize_schedule_durations(best_schedule)
        
        # Format itinerary
        itinerary = []
        for meeting in optimized_schedule:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": meeting['start_time'].strftime('%H:%M'),
                "end_time": meeting['end_time'].strftime('%H:%M')
            })
        
        output = {"itinerary": itinerary}
    else:
        output = {"itinerary": []}
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()