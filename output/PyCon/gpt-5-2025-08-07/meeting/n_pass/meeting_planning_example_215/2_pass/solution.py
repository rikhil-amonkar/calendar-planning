import json
from itertools import permutations
from datetime import datetime, timedelta

def main():
    # Travel times in minutes
    travel_times = {
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Richmond District', 'Bayview'): 26,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Richmond District'): 18
    }
    
    # Convert times to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = time_str.split(':')
            am_pm = minutes[-2:] if minutes[-2:] in ['AM', 'PM'] else None
            if am_pm:
                minutes = minutes[:-2]
            hours = int(hours)
            minutes = int(minutes)
            
            if am_pm == 'PM' and hours != 12:
                hours += 12
            elif am_pm == 'AM' and hours == 12:
                hours = 0
                
            return hours * 60 + minutes
        return int(time_str)
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        am_pm = "AM" if hours < 12 else "PM"
        if hours > 12:
            hours -= 12
        elif hours == 0:
            hours = 12
        return f"{hours}:{mins:02d} {am_pm}"
    
    # Friend constraints
    friends = {
        'Jessica': {
            'location': 'Embarcadero',
            'available_start': time_to_minutes('16:45'),  # 4:45 PM
            'available_end': time_to_minutes('19:00'),    # 7:00 PM
            'min_duration': 30
        },
        'Sandra': {
            'location': 'Richmond District',
            'available_start': time_to_minutes('18:30'),  # 6:30 PM
            'available_end': time_to_minutes('21:45'),    # 9:45 PM
            'min_duration': 120
        },
        'Jason': {
            'location': 'Fisherman\'s Wharf',
            'available_start': time_to_minutes('16:00'),  # 4:00 PM
            'available_end': time_to_minutes('16:45'),    # 4:45 PM
            'min_duration': 30
        }
    }
    
    start_time = time_to_minutes('9:00 AM')  # Start at Bayview at 9:00 AM
    current_location = 'Bayview'
    
    # Try all possible orders of meeting friends
    best_itinerary = []
    best_total_time = 0
    friend_names = list(friends.keys())
    
    for order in permutations(friend_names):
        itinerary = []
        current_time = start_time
        current_loc = current_location
        total_meeting_time = 0
        valid = True
        
        for friend in order:
            friend_info = friends[friend]
            meeting_loc = friend_info['location']
            
            # Calculate travel time
            travel_time = travel_times.get((current_loc, meeting_loc), float('inf'))
            
            # Arrival time at meeting location
            arrival_time = current_time + travel_time
            
            # Check if we can make it to the meeting within the friend's availability
            if arrival_time > friend_info['available_end']:
                valid = False
                break
            
            # Determine meeting start time (can't start before friend is available)
            meeting_start = max(arrival_time, friend_info['available_start'])
            
            # Check if we have enough time for minimum duration
            if meeting_start + friend_info['min_duration'] > friend_info['available_end']:
                valid = False
                break
            
            # Use maximum possible duration within constraints
            meeting_duration = min(
                friend_info['available_end'] - meeting_start,
                180  # Reasonable maximum for a single meeting
            )
            
            # Add travel segment if needed
            if current_loc != meeting_loc:
                itinerary.append({
                    "action": "travel",
                    "location": meeting_loc,
                    "start_time": minutes_to_time(current_time),
                    "end_time": minutes_to_time(current_time + travel_time)
                })
            
            # Add meeting segment
            itinerary.append({
                "action": "meet",
                "location": meeting_loc,
                "person": friend,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_start + meeting_duration)
            })
            
            # Update state
            current_time = meeting_start + meeting_duration
            current_loc = meeting_loc
            total_meeting_time += meeting_duration
        
        # Check if this itinerary is better than the current best
        if valid and total_meeting_time > best_total_time:
            best_total_time = total_meeting_time
            best_itinerary = itinerary.copy()
    
    # If no valid itinerary found with all friends, try subsets
    if not best_itinerary:
        # Try all possible subsets of friends
        from itertools import combinations
        
        for size in range(len(friend_names), 0, -1):
            for subset in combinations(friend_names, size):
                for order in permutations(subset):
                    itinerary = []
                    current_time = start_time
                    current_loc = current_location
                    total_meeting_time = 0
                    valid = True
                    
                    for friend in order:
                        friend_info = friends[friend]
                        meeting_loc = friend_info['location']
                        
                        travel_time = travel_times.get((current_loc, meeting_loc), float('inf'))
                        arrival_time = current_time + travel_time
                        
                        if arrival_time > friend_info['available_end']:
                            valid = False
                            break
                        
                        meeting_start = max(arrival_time, friend_info['available_start'])
                        
                        if meeting_start + friend_info['min_duration'] > friend_info['available_end']:
                            valid = False
                            break
                        
                        meeting_duration = min(
                            friend_info['available_end'] - meeting_start,
                            180
                        )
                        
                        if current_loc != meeting_loc:
                            itinerary.append({
                                "action": "travel",
                                "location": meeting_loc,
                                "start_time": minutes_to_time(current_time),
                                "end_time": minutes_to_time(current_time + travel_time)
                            })
                        
                        itinerary.append({
                            "action": "meet",
                            "location": meeting_loc,
                            "person": friend,
                            "start_time": minutes_to_time(meeting_start),
                            "end_time": minutes_to_time(meeting_start + meeting_duration)
                        })
                        
                        current_time = meeting_start + meeting_duration
                        current_loc = meeting_loc
                        total_meeting_time += meeting_duration
                    
                    if valid and total_meeting_time > best_total_time:
                        best_total_time = total_meeting_time
                        best_itinerary = itinerary.copy()
                        break
                    
                if best_itinerary:
                    break
            if best_itinerary:
                break
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()