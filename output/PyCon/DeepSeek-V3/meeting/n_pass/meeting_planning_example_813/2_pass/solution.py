import json
from datetime import datetime, timedelta

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Marina District': {
            'Embarcadero': 14, 'Bayview': 27, 'Union Square': 16, 'Chinatown': 15,
            'Sunset District': 19, 'Golden Gate Park': 18, 'Financial District': 17,
            'Haight-Ashbury': 16, 'Mission District': 20
        },
        'Embarcadero': {
            'Marina District': 12, 'Bayview': 21, 'Union Square': 10, 'Chinatown': 7,
            'Sunset District': 30, 'Golden Gate Park': 25, 'Financial District': 5,
            'Haight-Ashbury': 21, 'Mission District': 20
        },
        'Bayview': {
            'Marina District': 27, 'Embarcadero': 19, 'Union Square': 18, 'Chinatown': 19,
            'Sunset District': 23, 'Golden Gate Park': 22, 'Financial District': 19,
            'Haight-Ashbury': 19, 'Mission District': 13
        },
        'Union Square': {
            'Marina District': 18, 'Embarcadero': 11, 'Bayview': 15, 'Chinatown': 7,
            'Sunset District': 27, 'Golden Gate Park': 22, 'Financial District': 9,
            'Haight-Ashbury': 18, 'Mission District': 14
        },
        'Chinatown': {
            'Marina District': 12, 'Embarcadero': 5, 'Bayview': 20, 'Union Square': 7,
            'Sunset District': 29, 'Golden Gate Park': 23, 'Financial District': 5,
            'Haight-Ashbury': 19, 'Mission District': 17
        },
        'Sunset District': {
            'Marina District': 21, 'Embarcadero': 30, 'Bayview': 22, 'Union Square': 30,
            'Chinatown': 30, 'Golden Gate Park': 11, 'Financial District': 30,
            'Haight-Ashbury': 15, 'Mission District': 25
        },
        'Golden Gate Park': {
            'Marina District': 16, 'Embarcadero': 25, 'Bayview': 23, 'Union Square': 22,
            'Chinatown': 23, 'Sunset District': 10, 'Financial District': 26,
            'Haight-Ashbury': 7, 'Mission District': 17
        },
        'Financial District': {
            'Marina District': 15, 'Embarcadero': 4, 'Bayview': 19, 'Union Square': 9,
            'Chinatown': 5, 'Sunset District': 30, 'Golden Gate Park': 23,
            'Haight-Ashbury': 19, 'Mission District': 17
        },
        'Haight-Ashbury': {
            'Marina District': 17, 'Embarcadero': 20, 'Bayview': 18, 'Union Square': 19,
            'Chinatown': 19, 'Sunset District': 15, 'Golden Gate Park': 7,
            'Financial District': 21, 'Mission District': 11
        },
        'Mission District': {
            'Marina District': 19, 'Embarcadero': 19, 'Bayview': 14, 'Union Square': 15,
            'Chinatown': 16, 'Sunset District': 24, 'Golden Gate Park': 17,
            'Financial District': 15, 'Haight-Ashbury': 12
        }
    }

    # Define meeting constraints
    meetings = [
        {'person': 'Joshua', 'location': 'Embarcadero', 'start_window': '9:45', 'end_window': '18:00', 'duration': 105},
        {'person': 'Jeffrey', 'location': 'Bayview', 'start_window': '9:45', 'end_window': '20:15', 'duration': 75},
        {'person': 'Charles', 'location': 'Union Square', 'start_window': '10:45', 'end_window': '20:15', 'duration': 120},
        {'person': 'Joseph', 'location': 'Chinatown', 'start_window': '7:00', 'end_window': '15:30', 'duration': 60},
        {'person': 'Elizabeth', 'location': 'Sunset District', 'start_window': '9:00', 'end_window': '9:45', 'duration': 45},
        {'person': 'Matthew', 'location': 'Golden Gate Park', 'start_window': '11:00', 'end_window': '19:30', 'duration': 45},
        {'person': 'Carol', 'location': 'Financial District', 'start_window': '10:45', 'end_window': '11:15', 'duration': 15},
        {'person': 'Paul', 'location': 'Haight-Ashbury', 'start_window': '19:15', 'end_window': '20:30', 'duration': 15},
        {'person': 'Rebecca', 'location': 'Mission District', 'start_window': '17:00', 'end_window': '21:45', 'duration': 45}
    ]

    # Convert time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
            return hours * 60 + minutes
        return int(time_str) * 60

    # Convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Convert meetings to use minutes
    for meeting in meetings:
        meeting['start_window_min'] = time_to_minutes(meeting['start_window'])
        meeting['end_window_min'] = time_to_minutes(meeting['end_window'])

    # Sort meetings by end window (earlier deadlines first)
    meetings.sort(key=lambda x: x['end_window_min'])

    # Greedy scheduling algorithm
    def schedule_meetings(meetings, start_location='Marina District'):
        scheduled = []
        current_time = time_to_minutes('9:00')  # Start at 9:00 AM
        current_location = start_location
        
        for meeting in meetings:
            # Calculate earliest possible start time considering travel
            earliest_start = current_time
            if current_location != meeting['location']:
                travel_time = travel_times[current_location][meeting['location']]
                earliest_start += travel_time
            
            # Find the optimal start time within the meeting window
            start_time = max(earliest_start, meeting['start_window_min'])
            end_time = start_time + meeting['duration']
            
            # Check if meeting can be scheduled within its window
            if end_time <= meeting['end_window_min']:
                # Schedule this meeting
                scheduled.append({
                    'meeting': meeting,
                    'start_time': start_time,
                    'end_time': end_time,
                    'travel_from': current_location
                })
                current_time = end_time
                current_location = meeting['location']
        
        return scheduled

    # Try scheduling with different meeting orders to maximize number of meetings
    best_schedule = []
    
    # Try different sorting strategies
    strategies = [
        lambda x: x['end_window_min'],  # Earliest deadline first
        lambda x: x['duration'],  # Shortest duration first
        lambda x: x['start_window_min'],  # Earliest start window first
        lambda x: -len([m for m in meetings if travel_times[x['location']][m['location']] < 20])  # Most connected locations first
    ]
    
    for strategy in strategies:
        sorted_meetings = sorted(meetings, key=strategy)
        schedule = schedule_meetings(sorted_meetings)
        if len(schedule) > len(best_schedule):
            best_schedule = schedule

    # Build itinerary
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Marina District'
    
    for scheduled in best_schedule:
        meeting = scheduled['meeting']
        
        # Add travel if needed
        if current_location != meeting['location']:
            travel_time = travel_times[current_location][meeting['location']]
            travel_start = minutes_to_time(current_time)
            current_time += travel_time
            travel_end = minutes_to_time(current_time)
            itinerary.append({
                "action": "travel",
                "location": meeting['location'],
                "person": "",
                "start_time": travel_start,
                "end_time": travel_end
            })
            current_location = meeting['location']
        
        # Add meeting
        meeting_start = minutes_to_time(scheduled['start_time'])
        meeting_end = minutes_to_time(scheduled['end_time'])
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": meeting_start,
            "end_time": meeting_end
        })
        current_time = scheduled['end_time']
        current_location = meeting['location']

    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()