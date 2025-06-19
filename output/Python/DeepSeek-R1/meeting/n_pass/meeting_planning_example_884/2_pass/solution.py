import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times dictionary with corrected Golden Gate Park to Bayview time
    travel_times = {
        'Richmond District': {
            'Chinatown': 20, 'Sunset District': 11, 'Alamo Square': 13, 'Financial District': 22,
            'North Beach': 17, 'Embarcadero': 19, 'Presidio': 7, 'Golden Gate Park': 9, 'Bayview': 27
        },
        'Chinatown': {
            'Richmond District': 20, 'Sunset District': 29, 'Alamo Square': 17, 'Financial District': 5,
            'North Beach': 3, 'Embarcadero': 5, 'Presidio': 19, 'Golden Gate Park': 23, 'Bayview': 20
        },
        'Sunset District': {
            'Richmond District': 12, 'Chinatown': 30, 'Alamo Square': 17, 'Financial District': 30,
            'North Beach': 28, 'Embarcadero': 30, 'Presidio': 16, 'Golden Gate Park': 11, 'Bayview': 22
        },
        'Alamo Square': {
            'Richmond District': 11, 'Chinatown': 15, 'Sunset District': 16, 'Financial District': 17,
            'North Beach': 15, 'Embarcadero': 16, 'Presidio': 17, 'Golden Gate Park': 9, 'Bayview': 16
        },
        'Financial District': {
            'Richmond District': 21, 'Chinatown': 5, 'Sunset District': 30, 'Alamo Square': 17,
            'North Beach': 7, 'Embarcadero': 4, 'Presidio': 22, 'Golden Gate Park': 23, 'Bayview': 19
        },
        'North Beach': {
            'Richmond District': 18, 'Chinatown': 6, 'Sunset District': 27, 'Alamo Square': 16,
            'Financial District': 8, 'Embarcadero': 6, 'Presidio': 17, 'Golden Gate Park': 22, 'Bayview': 25
        },
        'Embarcadero': {
            'Richmond District': 21, 'Chinatown': 7, 'Sunset District': 30, 'Alamo Square': 19,
            'Financial District': 5, 'North Beach': 5, 'Presidio': 20, 'Golden Gate Park': 25, 'Bayview': 21
        },
        'Presidio': {
            'Richmond District': 7, 'Chinatown': 21, 'Sunset District': 15, 'Alamo Square': 19,
            'Financial District': 23, 'North Beach': 18, 'Embarcadero': 20, 'Golden Gate Park': 12, 'Bayview': 31
        },
        'Golden Gate Park': {
            'Richmond District': 7, 'Chinatown': 23, 'Sunset District': 10, 'Alamo Square': 9,
            'Financial District': 26, 'North Beach': 23, 'Embarcadero': 25, 'Presidio': 11, 'Bayview': 23  # Corrected from 22 to 23
        },
        'Bayview': {
            'Richmond District': 25, 'Chinatown': 19, 'Sunset District': 23, 'Alamo Square': 16,
            'Financial District': 19, 'North Beach': 22, 'Embarcadero': 19, 'Presidio': 32, 'Golden Gate Park': 22
        }
    }
    
    # Define friends with their constraints
    friends = [
        {'name': 'Robert', 'location': 'Chinatown', 'start_avail': time_to_minutes('7:45'), 'end_avail': time_to_minutes('17:30'), 'min_duration': 120},
        {'name': 'Matthew', 'location': 'Alamo Square', 'start_avail': time_to_minutes('8:45'), 'end_avail': time_to_minutes('13:45'), 'min_duration': 90},
        {'name': 'David', 'location': 'Sunset District', 'start_avail': time_to_minutes('12:30'), 'end_avail': time_to_minutes('19:45'), 'min_duration': 45},
        {'name': 'Jessica', 'location': 'Financial District', 'start_avail': time_to_minutes('9:30'), 'end_avail': time_to_minutes('18:45'), 'min_duration': 45},
        {'name': 'Mark', 'location': 'Embarcadero', 'start_avail': time_to_minutes('15:15'), 'end_avail': time_to_minutes('17:00'), 'min_duration': 45},
        {'name': 'Karen', 'location': 'Golden Gate Park', 'start_avail': time_to_minutes('19:30'), 'end_avail': time_to_minutes('22:00'), 'min_duration': 120},
        {'name': 'Laura', 'location': 'Bayview', 'start_avail': time_to_minutes('21:15'), 'end_avail': time_to_minutes('22:15'), 'min_duration': 15}
    ]
    
    # Starting point
    current_location = 'Richmond District'
    current_time = time_to_minutes('9:00')  # 9:00 AM
    itinerary = []
    
    # Schedule meetings in predefined order
    for friend in friends:
        # Get travel time to friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        # Meeting can start at the later of arrival time or friend's available start
        meeting_start = max(arrival_time, friend['start_avail'])
        meeting_end = meeting_start + friend['min_duration']
        
        # Check if meeting can be scheduled within friend's availability
        if meeting_end > friend['end_avail']:
            continue
        
        # Add meeting to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        # Update current time and location for next meeting
        current_time = meeting_end
        current_location = friend['location']
    
    # Output the itinerary as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()