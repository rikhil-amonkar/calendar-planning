import itertools
import json

def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return hour * 60 + minute

    # Convert minutes to time string (H:MM)
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"

    # Build travel_times dictionary
    travel_times = {
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Bayview'): 26,
        ('Richmond District', 'Union Square'): 21,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Chinatown'): 16,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Union Square'): 16,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'Union Square'): 7,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Union Square'): 9,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Marina District'): 25,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Union Square'): 17,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Bayview'): 15
    }

    # Define meetings with availability and duration
    meetings = [
        {
            'name': 'Margaret',
            'location': 'Bayview',
            'start_avail': time_to_minutes('9:30'),
            'end_avail': time_to_minutes('13:30'),
            'duration': 30
        },
        {
            'name': 'Kimberly',
            'location': 'Marina District',
            'start_avail': time_to_minutes('13:15'),
            'end_avail': time_to_minutes('16:45'),
            'duration': 15
        },
        {
            'name': 'Robert',
            'location': 'Chinatown',
            'start_avail': time_to_minutes('12:15'),
            'end_avail': time_to_minutes('20:15'),
            'duration': 15
        },
        {
            'name': 'Rebecca',
            'location': 'Financial District',
            'start_avail': time_to_minutes('13:15'),
            'end_avail': time_to_minutes('16:45'),
            'duration': 75
        },
        {
            'name': 'Kenneth',
            'location': 'Union Square',
            'start_avail': time_to_minutes('19:30'),
            'end_avail': time_to_minutes('21:15'),
            'duration': 75
        }
    ]

    # Start time and location
    start_time = time_to_minutes('9:00')
    start_loc = 'Richmond District'
    
    # Try to schedule from largest to smallest subset
    found = False
    best_itinerary = []
    
    # Iterate subset sizes from 5 down to 1
    for size in range(5, 0, -1):
        for subset in itertools.combinations(meetings, size):
            for perm in itertools.permutations(subset):
                current_time = start_time
                current_loc = start_loc
                itinerary = []
                valid = True
                
                for meeting in perm:
                    # Get travel time
                    travel_key = (current_loc, meeting['location'])
                    travel_duration = travel_times[travel_key]
                    current_time += travel_duration
                    
                    # Calculate meeting start and end times
                    meeting_start = max(current_time, meeting['start_avail'])
                    meeting_end = meeting_start + meeting['duration']
                    
                    # Check if meeting fits in availability window
                    if meeting_end > meeting['end_avail']:
                        valid = False
                        break
                    
                    # Add meeting to itinerary
                    itinerary.append({
                        'action': 'meet',
                        'location': meeting['location'],
                        'person': meeting['name'],
                        'start_time': minutes_to_time(meeting_start),
                        'end_time': minutes_to_time(meeting_end)
                    })
                    
                    # Update current time and location
                    current_time = meeting_end
                    current_loc = meeting['location']
                
                if valid:
                    found = True
                    best_itinerary = itinerary
                    break  # Break permutation loop
            if found:
                break  # Break subset combination loop
        if found:
            break  # Break subset size loop
    
    # Prepare result
    result = {"itinerary": best_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()