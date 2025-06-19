import json

def main():
    # Define travel times in minutes
    travel_times = {
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Financial District'): 20,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Financial District'): 17,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Mission District'): 17
    }
    
    # Start location and time (9:00 AM in minutes)
    start_location = 'The Castro'
    start_time = 9 * 60  # 540 minutes
    
    # Define meeting constraints
    meetings = [
        {
            'name': 'Laura',
            'location': 'Mission District',
            'start_avail': 12 * 60 + 15,  # 735 minutes (12:15 PM)
            'end_avail': 19 * 60 + 45,    # 1185 minutes (7:45 PM)
            'min_duration': 75
        },
        {
            'name': 'Anthony',
            'location': 'Financial District',
            'start_avail': 12 * 60 + 30,  # 750 minutes (12:30 PM)
            'end_avail': 14 * 60 + 45,    # 885 minutes (2:45 PM)
            'min_duration': 30
        }
    ]
    
    # List to store valid schedules
    candidates = []
    
    # Try both meeting orders: [0,1] and [1,0]
    orders = [[0, 1], [1, 0]]
    for order in orders:
        current_loc = start_location
        current_time = start_time
        schedule = []
        valid = True
        
        for idx in order:
            mtg = meetings[idx]
            # Get travel time between current location and meeting location
            travel_key = (current_loc, mtg['location'])
            if travel_key not in travel_times:
                valid = False
                break
            travel_duration = travel_times[travel_key]
            
            # Calculate arrival time at meeting location
            arrival_time = current_time + travel_duration
            if arrival_time < mtg['start_avail']:
                start_meeting = mtg['start_avail']
            else:
                start_meeting = arrival_time
            
            # Check if meeting fits within availability
            end_meeting = start_meeting + mtg['min_duration']
            if end_meeting > mtg['end_avail']:
                valid = False
                break
                
            # Record meeting details
            schedule.append((mtg['name'], mtg['location'], start_meeting, end_meeting))
            current_loc = mtg['location']
            current_time = end_meeting
        
        if valid:
            finish_time = current_time
            candidates.append((len(schedule), finish_time, schedule))
    
    # If no valid two-meeting schedules, try one-meeting schedules
    if not candidates:
        for i, mtg in enumerate(meetings):
            travel_key = (start_location, mtg['location'])
            if travel_key not in travel_times:
                continue
            travel_duration = travel_times[travel_key]
            
            arrival_time = start_time + travel_duration
            if arrival_time < mtg['start_avail']:
                start_meeting = mtg['start_avail']
            else:
                start_meeting = arrival_time
            
            end_meeting = start_meeting + mtg['min_duration']
            if end_meeting <= mtg['end_avail']:
                schedule = [(mtg['name'], mtg['location'], start_meeting, end_meeting)]
                candidates.append((1, end_meeting, schedule))
    
    # Select best candidate: maximize meetings, then minimize finish time
    if candidates:
        candidates.sort(key=lambda x: (-x[0], x[1]))
        best_candidate = candidates[0][2]
    else:
        best_candidate = []
    
    # Format the itinerary
    itinerary = []
    for mtg in best_candidate:
        name, loc, start_min, end_min = mtg
        # Convert minutes to "H:MM" format
        def format_time(mins):
            h = mins // 60
            m = mins % 60
            return f"{h}:{m:02d}"
        
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": format_time(start_min),
            "end_time": format_time(end_min)
        })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()