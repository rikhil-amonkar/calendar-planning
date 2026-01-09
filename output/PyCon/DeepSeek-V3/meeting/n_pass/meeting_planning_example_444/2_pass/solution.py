import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, '%H:%M')
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (from row to column)
    travel_times = {
        'Financial District': {
            'Financial District': 0,
            'Russian Hill': 10,
            'Sunset District': 31,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'Russian Hill': {
            'Financial District': 11,
            'Russian Hill': 0,
            'Sunset District': 23,
            'North Beach': 5,
            'The Castro': 21,
            'Golden Gate Park': 21
        },
        'Sunset District': {
            'Financial District': 30,
            'Russian Hill': 24,
            'Sunset District': 0,
            'North Beach': 29,
            'The Castro': 17,
            'Golden Gate Park': 11
        },
        'North Beach': {
            'Financial District': 8,
            'Russian Hill': 4,
            'Sunset District': 27,
            'North Beach': 0,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Financial District': 20,
            'Russian Hill': 18,
            'Sunset District': 17,
            'North Beach': 20,
            'The Castro': 0,
            'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Financial District': 26,
            'Russian Hill': 19,
            'Sunset District': 10,
            'North Beach': 24,
            'The Castro': 13,
            'Golden Gate Park': 0
        }
    }

    # Friend constraints
    friends = {
        'Ronald': {
            'location': 'Russian Hill',
            'available_start': time_to_minutes('13:45'),  # 1:45 PM
            'available_end': time_to_minutes('17:15'),    # 5:15 PM
            'min_duration': 105
        },
        'Patricia': {
            'location': 'Sunset District',
            'available_start': time_to_minutes('9:15'),   # 9:15 AM
            'available_end': time_to_minutes('22:00'),    # 10:00 PM
            'min_duration': 60
        },
        'Laura': {
            'location': 'North Beach',
            'available_start': time_to_minutes('12:30'),  # 12:30 PM
            'available_end': time_to_minutes('12:45'),    # 12:45 PM
            'min_duration': 15
        },
        'Emily': {
            'location': 'The Castro',
            'available_start': time_to_minutes('16:15'),  # 4:15 PM
            'available_end': time_to_minutes('18:30'),    # 6:30 PM
            'min_duration': 60
        },
        'Mary': {
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('15:00'),  # 3:00 PM
            'available_end': time_to_minutes('16:30'),    # 4:30 PM
            'min_duration': 60
        }
    }

    # Start at Financial District at 9:00 AM
    current_time = time_to_minutes('9:00')
    current_location = 'Financial District'
    max_end_time = time_to_minutes('22:00')  # End of day constraint

    itinerary = []
    visited_friends = []

    while current_time < max_end_time:
        # Find the next feasible friend to visit
        best_friend = None
        best_start_time = None
        best_end_time = None
        
        for friend, info in friends.items():
            if friend in visited_friends:
                continue
                
            location = info['location']
            available_start = info['available_start']
            available_end = info['available_end']
            min_duration = info['min_duration']
            
            # Calculate earliest possible start time considering travel
            travel_time = travel_times[current_location][location]
            earliest_start = max(current_time + travel_time, available_start)
            
            # Check if meeting is feasible
            if earliest_start + min_duration <= available_end and earliest_start + min_duration <= max_end_time:
                # Try to schedule at the earliest possible time
                potential_start = earliest_start
                potential_end = potential_start + min_duration
                
                if best_friend is None or potential_end < best_end_time:
                    best_friend = friend
                    best_start_time = potential_start
                    best_end_time = potential_end
        
        if best_friend is None:
            # No more feasible friends to visit
            break
        
        # Add travel to itinerary if needed
        travel_time_needed = travel_times[current_location][friends[best_friend]['location']]
        if travel_time_needed > 0 and best_start_time > current_time:
            itinerary.append({
                "action": "travel",
                "location": friends[best_friend]['location'],
                "person": "",
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(best_start_time)
            })
        
        # Add meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": friends[best_friend]['location'],
            "person": best_friend,
            "start_time": minutes_to_time(best_start_time),
            "end_time": minutes_to_time(best_end_time)
        })
        
        # Update state
        visited_friends.append(best_friend)
        current_time = best_end_time
        current_location = friends[best_friend]['location']

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()