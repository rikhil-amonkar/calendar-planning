import json
import itertools

def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1]) if len(parts) > 1 else 0
        return hours * 60 + minutes

    # Convert minutes back to time string
    def minutes_to_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"

    # Define symmetric travel times more efficiently
    travel_times = {}
    travel_data = [
        (('The Castro', 'Alamo Square'), 8),
        (('The Castro', 'Union Square'), 19),
        (('The Castro', 'Chinatown'), 20),
        (('Alamo Square', 'Union Square'), 15),
        (('Alamo Square', 'Chinatown'), 17),
        (('Union Square', 'Chinatown'), 7)
    ]
    
    for (loc1, loc2), minutes in travel_data:
        travel_times[(loc1, loc2)] = minutes
        travel_times[(loc2, loc1)] = minutes

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

        # Schedule meetings in order
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
            
            # Calculate maximum possible meeting end time
            meeting_end = min(meeting_start + friend['min_duration'], friend['end'])
            # If we can't meet minimum duration, skip
            if meeting_end - meeting_start < friend['min_duration']:
                valid = False
                break
                
            # Record this meeting
            itinerary_min.append({
                'start': meeting_start,
                'end': meeting_end,
                'friend': friend
            })
            
            # Update current time and location
            current_time = meeting_end
            current_loc = friend['location']
        
        if not valid:
            continue
            
        # Now try to extend meetings in reverse order
        extended_itinerary = itinerary_min.copy()
        # Start from last meeting and extend backwards
        for i in range(len(extended_itinerary)-1, -1, -1):
            current_meeting = extended_itinerary[i]
            friend = current_meeting['friend']
            
            # Determine how much we can extend this meeting
            if i == len(extended_itinerary)-1:
                # Last meeting: extend to end of window
                max_end = friend['end']
            else:
                next_meeting = extended_itinerary[i+1]
                # Travel time between current and next friend
                if current_meeting['friend']['location'] == next_meeting['friend']['location']:
                    travel_next = 0
                else:
                    key = (current_meeting['friend']['location'], next_meeting['friend']['location'])
                    travel_next = travel_times.get(key, float('inf'))
                # Must leave by: next meeting start - travel time
                max_end = next_meeting['start'] - travel_next
            
            # Extend current meeting as much as possible
            new_end = min(friend['end'], max_end)
            # Ensure we don't reduce meeting time below minimum
            new_end = max(new_end, current_meeting['end'])
            
            # Update the meeting end time
            extended_itinerary[i]['end'] = new_end
        
        # Calculate total friends and meeting time
        num_friends = len(extended_itinerary)
        total_time = sum(meet['end'] - meet['start'] for meet in extended_itinerary)
        
        # Update best candidate
        if num_friends > best_num_friends:
            best_candidate = extended_itinerary
            best_num_friends = num_friends
            best_total_time = total_time
        elif num_friends == best_num_friends and total_time > best_total_time:
            best_candidate = extended_itinerary
            best_total_time = total_time

    if best_candidate is None:
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