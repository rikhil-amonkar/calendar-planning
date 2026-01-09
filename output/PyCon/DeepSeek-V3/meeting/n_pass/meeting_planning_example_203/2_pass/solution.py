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

def find_feasible_itinerary():
    # Travel times in minutes
    travel_times = {
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Mission District'): 15,
        ('Mission District', 'Financial District'): 17,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Pacific Heights'): 16
    }
    
    # Friend constraints
    friends = {
        'David': {
            'location': 'Fisherman\'s Wharf',
            'available_start': time_to_minutes('10:45'),
            'available_end': time_to_minutes('15:30'),
            'min_duration': 15
        },
        'Timothy': {
            'location': 'Pacific Heights',
            'available_start': time_to_minutes('9:00'),
            'available_end': time_to_minutes('15:30'),
            'min_duration': 75
        },
        'Robert': {
            'location': 'Mission District',
            'available_start': time_to_minutes('12:15'),
            'available_end': time_to_minutes('19:45'),
            'min_duration': 90
        }
    }
    
    start_location = 'Financial District'
    start_time = time_to_minutes('9:00')
    
    def can_schedule_meeting(current_time, current_location, friend_name, meeting_start):
        friend = friends[friend_name]
        
        # Check if meeting fits in friend's availability
        if meeting_start < friend['available_start']:
            return False
        if meeting_start + friend['min_duration'] > friend['available_end']:
            return False
        
        # Check travel time
        travel_time = travel_times.get((current_location, friend['location']), float('inf'))
        arrival_time = current_time + travel_time
        
        return arrival_time <= meeting_start
    
    def find_best_schedule():
        # Try all possible orders
        best_schedule = None
        max_meetings = 0
        
        for order in permutations(['David', 'Timothy', 'Robert']):
            # Try to schedule all three in this order
            current_time = start_time
            current_location = start_location
            schedule = []
            successful_meetings = []
            
            for friend_name in order:
                friend = friends[friend_name]
                
                # Find earliest possible meeting time for this friend
                # We need to arrive by the meeting start time
                travel_time = travel_times.get((current_location, friend['location']), float('inf'))
                earliest_arrival = current_time + travel_time
                
                # Meeting must start no earlier than when we arrive and no earlier than friend's availability
                possible_start = max(earliest_arrival, friend['available_start'])
                
                if can_schedule_meeting(current_time, current_location, friend_name, possible_start):
                    meeting_end = possible_start + friend['min_duration']
                    
                    # Add travel segment if needed
                    if current_location != friend['location']:
                        schedule.append({
                            "action": "travel",
                            "location": friend['location'],
                            "person": "",
                            "start_time": minutes_to_time(current_time),
                            "end_time": minutes_to_time(current_time + travel_time)
                        })
                    
                    # Add meeting
                    schedule.append({
                        "action": "meet",
                        "location": friend['location'],
                        "person": friend_name,
                        "start_time": minutes_to_time(possible_start),
                        "end_time": minutes_to_time(meeting_end)
                    })
                    
                    successful_meetings.append(friend_name)
                    current_time = meeting_end
                    current_location = friend['location']
                else:
                    # Can't schedule this friend, skip
                    continue
            
            if len(successful_meetings) > max_meetings:
                max_meetings = len(successful_meetings)
                best_schedule = schedule
        
        return best_schedule if best_schedule else []
    
    # Find the best possible schedule
    itinerary = find_best_schedule()
    
    # If no schedule found with all three, try with two friends
    if not itinerary:
        # Try all combinations of two friends
        best_two_schedule = None
        max_two_meetings = 0
        
        for friend_pair in [['David', 'Timothy'], ['David', 'Robert'], ['Timothy', 'Robert']]:
            for order in permutations(friend_pair):
                current_time = start_time
                current_location = start_location
                schedule = []
                successful_meetings = []
                
                for friend_name in order:
                    friend = friends[friend_name]
                    
                    travel_time = travel_times.get((current_location, friend['location']), float('inf'))
                    earliest_arrival = current_time + travel_time
                    possible_start = max(earliest_arrival, friend['available_start'])
                    
                    if can_schedule_meeting(current_time, current_location, friend_name, possible_start):
                        meeting_end = possible_start + friend['min_duration']
                        
                        if current_location != friend['location']:
                            schedule.append({
                                "action": "travel",
                                "location": friend['location'],
                                "person": "",
                                "start_time": minutes_to_time(current_time),
                                "end_time": minutes_to_time(current_time + travel_time)
                            })
                        
                        schedule.append({
                            "action": "meet",
                            "location": friend['location'],
                            "person": friend_name,
                            "start_time": minutes_to_time(possible_start),
                            "end_time": minutes_to_time(meeting_end)
                        })
                        
                        successful_meetings.append(friend_name)
                        current_time = meeting_end
                        current_location = friend['location']
                
                if len(successful_meetings) > max_two_meetings:
                    max_two_meetings = len(successful_meetings)
                    best_two_schedule = schedule
        
        itinerary = best_two_schedule if best_two_schedule else []
    
    # If still no schedule, create a minimal one with the most available friend
    if not itinerary:
        # Timothy has the longest availability window
        friend_name = 'Timothy'
        friend = friends[friend_name]
        
        travel_time = travel_times.get((start_location, friend['location']), 0)
        arrival_time = start_time + travel_time
        meeting_start = max(arrival_time, friend['available_start'])
        
        itinerary = [
            {
                "action": "travel",
                "location": friend['location'],
                "person": "",
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(start_time + travel_time)
            },
            {
                "action": "meet",
                "location": friend['location'],
                "person": friend_name,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_start + friend['min_duration'])
            }
        ]
    
    return {"itinerary": itinerary}

def main():
    result = find_feasible_itinerary()
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()