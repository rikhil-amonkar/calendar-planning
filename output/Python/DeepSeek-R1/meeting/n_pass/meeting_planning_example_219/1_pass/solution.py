import json
import itertools

def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1]) if len(parts) > 1 else 0
        return hours * 60 + minutes

    # Convert minutes back to time string (without leading zero for hour)
    def minutes_to_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"

    # Travel times dictionary
    travel_times = {
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Chinatown'): 20,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Chinatown'): 16,
        ('Union Square', 'The Castro'): 19,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Union Square'): 7
    }

    # Constraints
    start_location = 'The Castro'
    start_time_min = time_to_minutes('9:00')  # 540 minutes

    # Friends data: name, location, start, end, min_duration (all in minutes)
    friends = [
        {
            'name': 'Emily',
            'location': 'Alamo Square',
            'start': time_to_minutes('11:45'),  # 705
            'end': time_to_minutes('15:15'),    # 915
            'min_duration': 105
        },
        {
            'name': 'Barbara',
            'location': 'Union Square',
            'start': time_to_minutes('16:45'),  # 1005
            'end': time_to_minutes('18:15'),    # 1095
            'min_duration': 60
        },
        {
            'name': 'William',
            'location': 'Chinatown',
            'start': time_to_minutes('17:15'),  # 1035
            'end': time_to_minutes('19:00'),    # 1140
            'min_duration': 105
        }
    ]

    # Generate all non-empty subsets of friends and their permutations
    all_permutations = []
    for r in range(1, len(friends)+1):
        for subset in itertools.combinations(friends, r):
            for perm in itertools.permutations(subset):
                all_permutations.append(perm)

    best_candidate = None
    best_num_friends = 0
    best_total_time = 0

    # Evaluate each permutation
    for perm in all_permutations:
        current_time = start_time_min
        current_loc = start_location
        itinerary_min = []  # list of meetings with start and end in minutes
        valid = True

        # Schedule with minimum durations
        for friend in perm:
            # Get travel time
            if current_loc == friend['location']:
                travel_time_val = 0
            else:
                key = (current_loc, friend['location'])
                if key not in travel_times:
                    valid = False
                    break
                travel_time_val = travel_times[key]
            
            arrival = current_time + travel_time_val
            meeting_start = max(arrival, friend['start'])
            meeting_end_min = meeting_start + friend['min_duration']
            
            if meeting_end_min > friend['end']:
                valid = False
                break
                
            # Record this meeting (minimal duration)
            itinerary_min.append({
                'start': meeting_start,
                'end': meeting_end_min,
                'friend': friend
            })
            
            # Update current time and location
            current_time = meeting_end_min
            current_loc = friend['location']
        
        if not valid:
            continue
            
        # Try to extend meetings in reverse order
        extended_itinerary = [None] * len(perm)
        # Start from last meeting
        if not itinerary_min:
            continue
        
        # Process last meeting: extend to end of window
        last_meeting = itinerary_min[-1]
        last_friend = last_meeting['friend']
        extended_end = last_friend['end']
        extended_itinerary[-1] = {
            'start': last_meeting['start'],
            'end': extended_end,
            'friend': last_friend
        }
        
        # Process previous meetings in reverse order
        for i in range(len(perm)-2, -1, -1):
            curr_meeting = itinerary_min[i]
            next_meeting = extended_itinerary[i+1]
            curr_friend = curr_meeting['friend']
            next_friend = next_meeting['friend']
            
            # Get travel time from current friend to next friend
            if curr_friend['location'] == next_friend['location']:
                travel_next = 0
            else:
                key = (curr_friend['location'], next_friend['location'])
                if key not in travel_times:
                    valid = False
                    break
                travel_next = travel_times[key]
            
            # Must leave current location by: next meeting start - travel_next
            leave_by = next_meeting['start'] - travel_next
            extended_end = min(curr_friend['end'], leave_by)
            
            # Ensure meeting duration is at least minimum
            if extended_end - curr_meeting['start'] < curr_friend['min_duration']:
                # Cannot extend beyond minimal; use minimal
                extended_end = curr_meeting['end']
            
            extended_itinerary[i] = {
                'start': curr_meeting['start'],
                'end': extended_end,
                'friend': curr_friend
            }
        
        if not valid:
            continue
            
        # Count the number of friends and total meeting time
        num_friends = len(perm)
        total_time = sum(meet['end'] - meet['start'] for meet in extended_itinerary)
        
        # Update best candidate
        if num_friends > best_num_friends:
            best_candidate = extended_itinerary
            best_num_friends = num_friends
            best_total_time = total_time
        elif num_friends == best_num_friends and total_time > best_total_time:
            best_candidate = extended_itinerary
            best_total_time = total_time

    # If no candidate found, default to meeting no one? But problem says meet as many as possible.
    if best_candidate is None:
        # This should not happen, but fallback
        result = {"itinerary": []}
    else:
        # Format the itinerary for output
        itinerary_json = []
        for meet in best_candidate:
            itinerary_json.append({
                "action": "meet",
                "location": meet['friend']['location'],
                "person": meet['friend']['name'],
                "start_time": minutes_to_time(meet['start']),
                "end_time": minutes_to_time(meet['end'])
            })
        result = {"itinerary": itinerary_json}
    
    # Output as JSON
    print(json.dumps(result))

if __name__ == "__main__":
    main()