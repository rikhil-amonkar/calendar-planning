import json

def main():
    # Travel times matrix (in minutes)
    travel_times = {
        'Nob Hill': {'Presidio': 17, 'North Beach': 8, 'Fisherman\'s Wharf': 11, 'Pacific Heights': 8},
        'Presidio': {'Nob Hill': 18, 'North Beach': 18, 'Fisherman\'s Wharf': 19, 'Pacific Heights': 11},
        'North Beach': {'Nob Hill': 7, 'Presidio': 17, 'Fisherman\'s Wharf': 5, 'Pacific Heights': 8},
        'Fisherman\'s Wharf': {'Nob Hill': 11, 'Presidio': 17, 'North Beach': 6, 'Pacific Heights': 12},
        'Pacific Heights': {'Nob Hill': 8, 'Presidio': 11, 'North Beach': 9, 'Fisherman\'s Wharf': 13}
    }
    
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.replace('AM', '').replace('PM', '').split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        if 'PM' in time_str and hour != 12:
            hour += 12
        if 'AM' in time_str and hour == 12:
            hour = 0
        return hour * 60 + minute

    # Convert minutes to time string (24-hour format)
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Constraints
    start_time = time_to_minutes('9:00AM')
    friends = [
        {'name': 'Jeffrey', 'location': 'Presidio', 'start': time_to_minutes('8:00AM'), 
         'end': time_to_minutes('10:00AM'), 'min_duration': 105},
        {'name': 'Steven', 'location': 'North Beach', 'start': time_to_minutes('1:30PM'), 
         'end': time_to_minutes('10:00PM'), 'min_duration': 45},
        {'name': 'Barbara', 'location': 'Fisherman\'s Wharf', 'start': time_to_minutes('6:00PM'), 
         'end': time_to_minutes('9:30PM'), 'min_duration': 30},
        {'name': 'John', 'location': 'Pacific Heights', 'start': time_to_minutes('9:00AM'), 
         'end': time_to_minutes('1:30PM'), 'min_duration': 15}
    ]
    
    # Initialize variables
    current_location = 'Nob Hill'
    current_time = start_time
    itinerary = []
    
    # Process each friend in optimal order
    for friend in friends:
        # Travel to friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Calculate meeting start and end times
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = min(friend['end'], meeting_start + friend['min_duration'])
        
        # Adjust if meeting time is insufficient
        if meeting_end - meeting_start < friend['min_duration']:
            meeting_end = friend['end']
            if meeting_end - meeting_start < friend['min_duration']:
                continue  # Skip friend if minimum can't be met
        
        # Add meeting to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        # Update current location and time
        current_location = friend['location']
        current_time = meeting_end
    
    # Output result
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()