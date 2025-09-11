import json

def main():
    # Define travel times between locations
    travel_times = {
        'Haight-Ashbury': {
            'Russian Hill': 17,
            'Fisherman\'s Wharf': 23,
            'Nob Hill': 15,
            'Golden Gate Park': 7,
            'Alamo Square': 5,
            'Pacific Heights': 12
        },
        'Russian Hill': {
            'Haight-Ashbury': 17,
            'Fisherman\'s Wharf': 7,
            'Nob Hill': 5,
            'Golden Gate Park': 21,
            'Alamo Square': 15,
            'Pacific Heights': 7
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22,
            'Russian Hill': 7,
            'Nob Hill': 11,
            'Golden Gate Park': 25,
            'Alamo Square': 20,
            'Pacific Heights': 12
        },
        'Nob Hill': {
            'Haight-Ashbury': 13,
            'Russian Hill': 5,
            'Fisherman\'s Wharf': 11,
            'Golden Gate Park': 17,
            'Alamo Square': 11,
            'Pacific Heights': 8
        },
        'Golden Gate Park': {
            'Haight-Ashbury': 7,
            'Russian Hill': 19,
            'Fisherman\'s Wharf': 24,
            'Nob Hill': 20,
            'Alamo Square': 10,
            'Pacific Heights': 16
        },
        'Alamo Square': {
            'Haight-Ashbury': 5,
            'Russian Hill': 13,
            'Fisherman\'s Wharf': 19,
            'Nob Hill': 11,
            'Golden Gate Park': 9,
            'Pacific Heights': 10
        },
        'Pacific Heights': {
            'Haight-Ashbury': 11,
            'Russian Hill': 7,
            'Fisherman\'s Wharf': 13,
            'Nob Hill': 8,
            'Golden Gate Park': 15,
            'Alamo Square': 10
        }
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return hour * 60 + minute - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(minutes):
        total_minutes = minutes + 540
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{hours}:{mins:02d}"

    # Define friends with their constraints
    friends = [
        {
            'name': 'Stephanie',
            'location': 'Russian Hill',
            'start_avail': time_to_minutes('20:00'),
            'end_avail': time_to_minutes('20:45'),
            'min_duration': 15
        },
        {
            'name': 'Kevin',
            'location': 'Fisherman\'s Wharf',
            'start_avail': time_to_minutes('19:15'),
            'end_avail': time_to_minutes('21:45'),
            'min_duration': 75
        },
        {
            'name': 'Robert',
            'location': 'Nob Hill',
            'start_avail': time_to_minutes('7:45'),
            'end_avail': time_to_minutes('10:30'),
            'min_duration': 90
        },
        {
            'name': 'Steven',
            'location': 'Golden Gate Park',
            'start_avail': time_to_minutes('8:30'),
            'end_avail': time_to_minutes('17:00'),
            'min_duration': 75
        },
        {
            'name': 'Anthony',
            'location': 'Alamo Square',
            'start_avail': time_to_minutes('7:45'),
            'end_avail': time_to_minutes('19:45'),
            'min_duration': 15
        },
        {
            'name': 'Sandra',
            'location': 'Pacific Heights',
            'start_avail': time_to_minutes('14:45'),
            'end_avail': time_to_minutes('21:45'),
            'min_duration': 45
        }
    ]

    # Initialize current time and location
    current_time = 0  # 9:00 AM
    current_location = 'Haight-Ashbury'
    itinerary = []

    # Helper function to schedule a meeting
    def schedule_meeting(friend, current_time, current_location):
        loc = friend['location']
        travel_time = travel_times[current_location][loc]
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, friend['start_avail'])
        end_time = start_time + friend['min_duration']
        
        if end_time > friend['end_avail']:
            return None, current_time, current_location
        
        meeting = {
            'action': 'meet',
            'location': loc,
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        }
        return meeting, end_time, loc

    # Schedule meetings in optimal order based on analysis
    meeting_order = ['Steven', 'Anthony', 'Sandra', 'Stephanie', 'Kevin']
    for name in meeting_order:
        friend = next(f for f in friends if f['name'] == name)
        meeting, new_time, new_loc = schedule_meeting(friend, current_time, current_location)
        if meeting is not None:
            itinerary.append(meeting)
            current_time = new_time
            current_location = new_loc

    # Output the itinerary as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()