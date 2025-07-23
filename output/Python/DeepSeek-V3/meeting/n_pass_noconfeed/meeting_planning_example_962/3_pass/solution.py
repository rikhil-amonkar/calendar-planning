import json
from itertools import permutations

# Travel times in minutes between locations
travel_times = {
    'The Castro': {
        'SoMa': 15,
        'Financial District': 18,
        'Mission District': 12,
        'Tenderloin': 20,
        'North Beach': 22
    },
    'SoMa': {
        'The Castro': 15,
        'Financial District': 8,
        'Mission District': 10,
        'Tenderloin': 12,
        'North Beach': 18
    },
    'Financial District': {
        'The Castro': 18,
        'SoMa': 8,
        'Mission District': 15,
        'Tenderloin': 10,
        'North Beach': 12
    },
    'Mission District': {
        'The Castro': 12,
        'SoMa': 10,
        'Financial District': 15,
        'Tenderloin': 18,
        'North Beach': 20
    },
    'Tenderloin': {
        'The Castro': 20,
        'SoMa': 12,
        'Financial District': 10,
        'Mission District': 18,
        'North Beach': 8
    },
    'North Beach': {
        'The Castro': 22,
        'SoMa': 18,
        'Financial District': 12,
        'Mission District': 20,
        'Tenderloin': 8
    }
}

# Meetings with time windows and durations (in hours)
meetings = [
    {
        'person': 'A',
        'location': 'Financial District',
        'start': 9.5,  # 9:30 AM
        'end': 11.0,   # 11:00 AM
        'duration': 0.5
    },
    {
        'person': 'B',
        'location': 'SoMa',
        'start': 10.0,  # 10:00 AM
        'end': 12.0,   # 12:00 PM
        'duration': 1.0
    },
    {
        'person': 'C',
        'location': 'Mission District',
        'start': 11.0,  # 11:00 AM
        'end': 12.5,   # 12:30 PM
        'duration': 0.5
    },
    {
        'person': 'D',
        'location': 'North Beach',
        'start': 11.5,  # 11:30 AM
        'end': 13.5,   # 1:30 PM
        'duration': 1.0
    }
]

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule(meeting_order):
    current_location = 'The Castro'
    current_time = 9.0  # 9:00 AM
    itinerary = []
    
    for meeting in meeting_order:
        # Calculate travel time in hours
        travel_time = travel_times[current_location][meeting['location']] / 60.0
        arrival_time = current_time + travel_time
        
        # Determine when we can start the meeting
        start_time = max(arrival_time, meeting['start'])
        end_time = start_time + meeting['duration']
        
        # Check if we can complete the meeting within the time window
        if end_time <= meeting['end']:
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['person'],
                'start_time': float_to_time(start_time),
                'end_time': float_to_time(end_time)
            })
            current_location = meeting['location']
            current_time = end_time
        else:
            return None  # This order doesn't work
    
    return itinerary

def main():
    # Try all possible permutations of meeting orders
    for meeting_order in permutations(meetings):
        itinerary = calculate_schedule(meeting_order)
        if itinerary:
            print(json.dumps({'itinerary': itinerary}, indent=2))
            return
    
    # If no valid order found
    print(json.dumps({'itinerary': []}, indent=2))

if __name__ == '__main__':
    main()