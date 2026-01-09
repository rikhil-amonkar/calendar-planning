import json
from datetime import datetime, timedelta

def main():
    # Travel times in minutes
    travel_times = {
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Embarcadero'): 19,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Mission District'): 20
    }
    
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = time_str.split(':')
            am_pm = minutes[-2:]
            minutes = minutes[:-2] if am_pm in ['AM', 'PM'] else minutes
            hours = int(hours)
            minutes = int(minutes)
            if am_pm == 'PM' and hours != 12:
                hours += 12
            elif am_pm == 'AM' and hours == 12:
                hours = 0
            return hours * 60 + minutes
        return int(time_str)
    
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
        'Patricia': {
            'location': 'Nob Hill',
            'available_start': time_to_minutes('18:30'),
            'available_end': time_to_minutes('21:45'),
            'min_duration': 90
        },
        'Ashley': {
            'location': 'Mission District',
            'available_start': time_to_minutes('20:30'),
            'available_end': time_to_minutes('21:15'),
            'min_duration': 45
        },
        'Timothy': {
            'location': 'Embarcadero',
            'available_start': time_to_minutes('9:45'),
            'available_end': time_to_minutes('17:45'),
            'min_duration': 120
        }
    }
    
    start_location = 'Russian Hill'
    start_time = time_to_minutes('9:00')
    
    def can_schedule_meeting(current_time, current_location, friend_name):
        """Check if we can schedule a meeting with this friend given current time and location"""
        friend = friends[friend_name]
        travel_time = travel_times.get((current_location, friend['location']), float('inf'))
        
        # Earliest we can arrive
        arrival_time = current_time + travel_time
        
        # If we arrive before their availability starts, wait until they're available
        meeting_start = max(arrival_time, friend['available_start'])
        
        # Check if we can have the minimum duration
        meeting_end = meeting_start + friend['min_duration']
        
        if meeting_end <= friend['available_end']:
            return True, meeting_start, meeting_end
        else:
            return False, None, None
    
    def find_best_itinerary():
        """Find the best itinerary using a greedy approach"""
        best_itinerary = []
        max_meetings = 0
        
        # Try all possible orders of meeting friends
        from itertools import permutations
        for order in permutations(['Timothy', 'Patricia', 'Ashley']):
            itinerary = []
            current_time = start_time
            current_location = start_location
            successful_meetings = 0
            
            for friend_name in order:
                can_meet, meeting_start, meeting_end = can_schedule_meeting(
                    current_time, current_location, friend_name)
                
                if can_meet:
                    itinerary.append({
                        "action": "meet",
                        "location": friends[friend_name]['location'],
                        "person": friend_name,
                        "start_time": minutes_to_time(meeting_start),
                        "end_time": minutes_to_time(meeting_end)
                    })
                    current_time = meeting_end
                    current_location = friends[friend_name]['location']
                    successful_meetings += 1
                else:
                    # Can't meet this friend, skip and continue with others
                    continue
            
            # Update best itinerary if we found more meetings
            if successful_meetings > max_meetings:
                best_itinerary = itinerary
                max_meetings = successful_meetings
            elif successful_meetings == max_meetings and successful_meetings > 0:
                # If same number of meetings, prefer longer total duration
                current_duration = sum([friends[item['person']]['min_duration'] for item in itinerary])
                best_duration = sum([friends[item['person']]['min_duration'] for item in best_itinerary])
                if current_duration > best_duration:
                    best_itinerary = itinerary
        
        return best_itinerary
    
    # Find the best itinerary
    itinerary = find_best_itinerary()
    
    # If we couldn't meet all three, try to optimize for the two we can meet
    if len(itinerary) < 3:
        # Try all pairs
        friend_pairs = [['Timothy', 'Patricia'], ['Timothy', 'Ashley'], ['Patricia', 'Ashley']]
        
        for pair in friend_pairs:
            from itertools import permutations
            for order in permutations(pair):
                temp_itinerary = []
                current_time = start_time
                current_location = start_location
                successful_meetings = 0
                
                for friend_name in order:
                    can_meet, meeting_start, meeting_end = can_schedule_meeting(
                        current_time, current_location, friend_name)
                    
                    if can_meet:
                        temp_itinerary.append({
                            "action": "meet",
                            "location": friends[friend_name]['location'],
                            "person": friend_name,
                            "start_time": minutes_to_time(meeting_start),
                            "end_time": minutes_to_time(meeting_end)
                        })
                        current_time = meeting_end
                        current_location = friends[friend_name]['location']
                        successful_meetings += 1
                    else:
                        break
                
                # Update if this is better than current best
                if successful_meetings > len(itinerary):
                    itinerary = temp_itinerary
                elif successful_meetings == len(itinerary) and successful_meetings > 0:
                    current_duration = sum([friends[item['person']]['min_duration'] for item in temp_itinerary])
                    best_duration = sum([friends[item['person']]['min_duration'] for item in itinerary])
                    if current_duration > best_duration:
                        itinerary = temp_itinerary
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()