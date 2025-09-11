import itertools
import json

def main():
    # Define travel times between locations (in minutes)
    travel_times = {
        'Financial District': {
            'Fisherman\'s Wharf': 10,
            'Pacific Heights': 13,
            'Mission District': 17
        },
        'Fisherman\'s Wharf': {
            'Financial District': 11,
            'Pacific Heights': 12,
            'Mission District': 22
        },
        'Pacific Heights': {
            'Financial District': 13,
            'Fisherman\'s Wharf': 13,
            'Mission District': 15
        },
        'Mission District': {
            'Financial District': 17,
            'Fisherman\'s Wharf': 22,
            'Pacific Heights': 16
        }
    }
    
    # Convert time strings to minutes since 9:00 AM
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute
    
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Define friends' constraints
    friends = [
        {
            'name': 'David',
            'location': 'Fisherman\'s Wharf',
            'available_start': time_to_minutes('10:45'),
            'available_end': time_to_minutes('15:30'),
            'min_duration': 15
        },
        {
            'name': 'Timothy',
            'location': 'Pacific Heights',
            'available_start': time_to_minutes('9:00'),
            'available_end': time_to_minutes('15:30'),
            'min_duration': 75
        },
        {
            'name': 'Robert',
            'location': 'Mission District',
            'available_start': time_to_minutes('12:15'),
            'available_end': time_to_minutes('19:45'),
            'min_duration': 90
        }
    ]
    
    start_location = 'Financial District'
    start_time = 0  # 9:00 AM in minutes since 9:00 AM
    
    # Function to schedule a sequence of meetings
    def schedule_sequence(sequence):
        current_location = start_location
        current_time = start_time
        itinerary = []
        for friend in sequence:
            # Travel to friend's location
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            # Wait if arriving before friend is available
            meeting_start = max(arrival_time, friend['available_start'])
            meeting_end = meeting_start + friend['min_duration']
            # Check if meeting is within friend's availability
            if meeting_end > friend['available_end']:
                return None
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']
        return itinerary
    
    # Try to schedule all 3 friends
    best_itinerary = None
    for sequence in itertools.permutations(friends):
        itinerary = schedule_sequence(sequence)
        if itinerary is not None:
            best_itinerary = itinerary
            break
    
    # If not all 3, try subsets of 2 friends
    if best_itinerary is None:
        for combo in itertools.combinations(friends, 2):
            for sequence in itertools.permutations(combo):
                itinerary = schedule_sequence(sequence)
                if itinerary is not None:
                    best_itinerary = itinerary
                    break
            if best_itinerary is not None:
                break
    
    # If not 2, try individual friends
    if best_itinerary is None:
        for friend in friends:
            itinerary = schedule_sequence([friend])
            if itinerary is not None:
                best_itinerary = itinerary
                break
    
    # Output the result
    result = {
        'itinerary': best_itinerary if best_itinerary is not None else []
    }
    print(json.dumps(result))

if __name__ == '__main__':
    main()