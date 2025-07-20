import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times dictionary
    travel_times = {
        'Sunset District': {'North Beach': 29, 'Union Square': 30, 'Alamo Square': 17},
        'North Beach': {'Sunset District': 27, 'Union Square': 7, 'Alamo Square': 16},
        'Union Square': {'Sunset District': 26, 'North Beach': 10, 'Alamo Square': 15},
        'Alamo Square': {'Sunset District': 16, 'North Beach': 15, 'Union Square': 14}
    }
    
    # Define friends with their details (converted to minutes)
    friends = {
        'Sarah': {
            'location': 'North Beach',
            'start': time_to_minutes("16:00"),
            'end': time_to_minutes("18:15"),
            'duration': 60
        },
        'Jeffrey': {
            'location': 'Union Square',
            'start': time_to_minutes("15:00"),
            'end': time_to_minutes("22:00"),
            'duration': 75
        },
        'Brian': {
            'location': 'Alamo Square',
            'start': time_to_minutes("16:00"),
            'end': time_to_minutes("17:30"),
            'duration': 75
        }
    }
    
    start_time = time_to_minutes("9:00")
    start_location = 'Sunset District'
    best_schedule = None
    
    # Try schedules with 3, 2, and 1 meetings
    for num_meetings in [3, 2, 1]:
        for perm in itertools.permutations(friends.keys(), num_meetings):
            current_time = start_time
            current_location = start_location
            itinerary = []
            feasible = True
            
            for friend in perm:
                friend_info = friends[friend]
                location = friend_info['location']
                
                # Travel to the friend's location
                current_time += travel_times[current_location][location]
                
                # Check if we arrived after the friend's availability window
                if current_time > friend_info['end']:
                    feasible = False
                    break
                
                # Wait until the friend becomes available if necessary
                if current_time < friend_info['start']:
                    current_time = friend_info['start']
                
                # Calculate meeting end time
                meeting_end = current_time + friend_info['duration']
                
                # Check if meeting fits within availability
                if meeting_end > friend_info['end']:
                    feasible = False
                    break
                
                # Add meeting to itinerary
                itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': friend,
                    'start_time': minutes_to_time(current_time),
                    'end_time': minutes_to_time(meeting_end)
                })
                
                # Update current time and location
                current_time = meeting_end
                current_location = location
            
            if feasible:
                candidate = {
                    'num_meetings': num_meetings,
                    'end_time': current_time,
                    'itinerary': itinerary
                }
                
                # Update best_schedule if this candidate is better
                if best_schedule is None:
                    best_schedule = candidate
                else:
                    if candidate['num_meetings'] > best_schedule['num_meetings']:
                        best_schedule = candidate
                    elif candidate['num_meetings'] == best_schedule['num_meetings']:
                        if candidate['end_time'] < best_schedule['end_time']:
                            best_schedule = candidate
    
    # Prepare output itinerary (empty if no feasible meetings)
    output_itinerary = best_schedule['itinerary'] if best_schedule else []
    
    # Output as JSON
    result = {'itinerary': output_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()