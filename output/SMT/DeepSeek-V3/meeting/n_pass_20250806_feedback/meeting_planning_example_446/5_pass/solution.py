from z3 import *
import json
from datetime import datetime, timedelta

def solve_scheduling():
    # Initialize solver with a longer timeout
    s = Solver()
    s.set("timeout", 60000)  # 60 second timeout

    # Define districts and their indices
    districts = {
        'Richmond': 0,
        'Marina': 1,
        'Chinatown': 2,
        'Financial': 3,
        'Bayview': 4,
        'Union Square': 5
    }

    # Travel times matrix (minutes)
    travel_times = [
        [0, 9, 20, 22, 26, 21],    # Richmond
        [11, 0, 16, 17, 27, 16],    # Marina
        [20, 12, 0, 5, 22, 7],      # Chinatown
        [21, 15, 5, 0, 19, 9],      # Financial
        [25, 25, 18, 19, 0, 17],    # Bayview
        [20, 18, 7, 9, 15, 0]       # Union Square
    ]

    # Friends data sorted by priority (longer meetings first)
    friends = [
        {'name': 'Rebecca', 'district': 'Financial', 
         'start_avail': 13*60+15, 'end_avail': 16*60+45, 'min_dur': 75},
        {'name': 'Kenneth', 'district': 'Union Square', 
         'start_avail': 19*60+30, 'end_avail': 21*60+15, 'min_dur': 75},
        {'name': 'Margaret', 'district': 'Bayview', 
         'start_avail': 9*60+30, 'end_avail': 13*60+30, 'min_dur': 30},
        {'name': 'Kimberly', 'district': 'Marina', 
         'start_avail': 13*60+15, 'end_avail': 16*60+45, 'min_dur': 15},
        {'name': 'Robert', 'district': 'Chinatown', 
         'start_avail': 12*60+15, 'end_avail': 20*60+15, 'min_dur': 15}
    ]

    # Current state
    current_location = districts['Richmond']
    current_time = 9 * 60  # 9:00 AM in minutes

    # Create meeting variables
    meetings = []
    for friend in friends:
        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        s.add(start >= friend['start_avail'])
        s.add(end <= friend['end_avail'])
        s.add(end == start + friend['min_dur'])
        meetings.append({
            'name': friend['name'],
            'district': friend['district'],
            'start': start,
            'end': end
        })

    # Generate all possible meeting orders
    from itertools import permutations
    for order in permutations(range(len(meetings))):
        # Reset constraints for each order
        temp_s = Solver()
        temp_s.set("timeout", 30000)
        
        # Add basic meeting constraints
        for meeting in meetings:
            temp_s.add(meeting['start'] >= friends[order.index(meetings.index(meeting))]['start_avail'])
            temp_s.add(meeting['end'] <= friends[order.index(meetings.index(meeting))]['end_avail'])
            temp_s.add(meeting['end'] == meeting['start'] + friends[order.index(meetings.index(meeting))]['min_dur'])
        
        # Add sequencing constraints for this order
        prev_end = current_time
        prev_loc = current_location
        for i in order:
            meeting = meetings[i]
            travel = travel_times[prev_loc][districts[meeting['district']]]
            temp_s.add(meeting['start'] >= prev_end + travel)
            prev_end = meeting['end']
            prev_loc = districts[meeting['district']]
        
        # Check if this order works
        if temp_s.check() == sat:
            model = temp_s.model()
            itinerary = []
            for meeting in meetings:
                start_val = model.eval(meeting['start']).as_long()
                end_val = model.eval(meeting['end']).as_long()
                start_time = f"{start_val//60:02d}:{start_val%60:02d}"
                end_time = f"{end_val//60:02d}:{end_val%60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meeting['name'],
                    "location": meeting['district'],
                    "start_time": start_time,
                    "end_time": end_time
                })
            
            # Sort by start time
            itinerary.sort(key=lambda x: x['start_time'])
            return {"status": "success", "itinerary": itinerary}
    
    return {"status": "failed", "reason": "No possible schedule meets all constraints"}

# Run and print results
result = solve_scheduling()
print(json.dumps(result, indent=2))