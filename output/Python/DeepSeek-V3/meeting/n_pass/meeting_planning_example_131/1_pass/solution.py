import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Input parameters
    travel_times = {
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Marina District'): 6,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Marina District'): 10,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Presidio'): 10,
    }
    
    # Correcting typo in Marina District key
    travel_times[('Marina District', 'Pacific Heights')] = 7
    travel_times[('Marina District', 'Presidio')] = 10
    
    start_location = 'Pacific Heights'
    start_time = '9:00'
    
    jason_location = 'Presidio'
    jason_window = ('10:00', '16:15')
    jason_duration = 90
    
    kenneth_location = 'Marina District'
    kenneth_window = ('15:30', '16:45')
    kenneth_duration = 45
    
    # Convert all times to minutes
    current_time = time_to_minutes(start_time)
    jason_start = time_to_minutes(jason_window[0])
    jason_end = time_to_minutes(jason_window[1])
    kenneth_start = time_to_minutes(kenneth_window[0])
    kenneth_end = time_to_minutes(kenneth_window[1])
    
    # Possible meeting orders
    meeting_orders = [
        ['Jason', 'Kenneth'],
        ['Kenneth', 'Jason']
    ]
    
    best_schedule = None
    best_meetings = 0
    
    for order in meeting_orders:
        itinerary = []
        current_loc = start_location
        current_time_temp = current_time
        meetings = 0
        
        for person in order:
            if person == 'Jason':
                loc = jason_location
                window_start = jason_start
                window_end = jason_end
                duration = jason_duration
            else:
                loc = kenneth_location
                window_start = kenneth_start
                window_end = kenneth_end
                duration = kenneth_duration
            
            # Calculate travel time
            travel_time = travel_times[(current_loc, loc)]
            arrival_time = current_time_temp + travel_time
            
            # Find meeting window
            meeting_start = max(arrival_time, window_start)
            meeting_end = meeting_start + duration
            
            if meeting_end <= window_end:
                itinerary.append({
                    'action': 'meet',
                    'location': loc,
                    'person': person,
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                current_time_temp = meeting_end
                current_loc = loc
                meetings += 1
            else:
                break
        
        if meetings > best_meetings:
            best_meetings = meetings
            best_schedule = itinerary
    
    # Check if we can meet both
    if best_meetings == 2:
        return best_schedule
    else:
        # Try to meet just one with maximum time
        # Try Jason first
        jason_itinerary = []
        travel_time = travel_times[(start_location, jason_location)]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, jason_start)
        meeting_end = min(meeting_start + jason_duration, jason_end)
        if meeting_end - meeting_start >= jason_duration:
            jason_itinerary.append({
                'action': 'meet',
                'location': jason_location,
                'person': 'Jason',
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
        
        # Try Kenneth
        kenneth_itinerary = []
        travel_time = travel_times[(start_location, kenneth_location)]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, kenneth_start)
        meeting_end = min(meeting_start + kenneth_duration, kenneth_end)
        if meeting_end - meeting_start >= kenneth_duration:
            kenneth_itinerary.append({
                'action': 'meet',
                'location': kenneth_location,
                'person': 'Kenneth',
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
        
        # Choose the one that gives more meeting time
        if jason_itinerary and kenneth_itinerary:
            jason_time = time_to_minutes(jason_itinerary[0]['end_time']) - time_to_minutes(jason_itinerary[0]['start_time'])
            kenneth_time = time_to_minutes(kenneth_itinerary[0]['end_time']) - time_to_minutes(kenneth_itinerary[0]['start_time'])
            if jason_time >= kenneth_time:
                return jason_itinerary
            else:
                return kenneth_itinerary
        elif jason_itinerary:
            return jason_itinerary
        elif kenneth_itinerary:
            return kenneth_itinerary
        else:
            return []

def main():
    schedule = calculate_schedule()
    result = {
        "itinerary": schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()