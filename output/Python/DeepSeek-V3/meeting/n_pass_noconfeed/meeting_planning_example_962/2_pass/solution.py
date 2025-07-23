import json
from itertools import permutations

# Travel times dictionary (same as before)
travel_times = {
    # ... (keep the same travel_times dictionary)
}

# Meeting constraints (same as before)
meetings = [
    # ... (keep the same meetings list)
]

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule():
    # Sort meetings by start time
    sorted_meetings = sorted(meetings, key=lambda x: x['start'])
    
    current_location = 'The Castro'
    current_time = 9.0  # 9:00 AM
    itinerary = []
    
    for meeting in sorted_meetings:
        # Calculate travel time in hours
        travel_time = travel_times[current_location][meeting['location']] / 60.0
        arrival_time = current_time + travel_time
        
        # Determine when we can start the meeting
        if arrival_time <= meeting['start']:
            start_time = meeting['start']  # Wait until meeting window opens
        else:
            start_time = arrival_time  # Arrive after window opens
            
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
            # Skip this meeting if it doesn't fit
            continue
    
    return itinerary if itinerary else None

def main():
    itinerary = calculate_schedule()
    if itinerary:
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print(json.dumps({'itinerary': []}, indent=2))

if __name__ == '__main__':
    main()