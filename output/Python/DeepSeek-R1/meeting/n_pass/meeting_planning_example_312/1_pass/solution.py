# SOLUTION:
import itertools
import json

def main():
    # Define constraints in minutes since 9:00 AM
    constraints = {
        "Sunset District": {"person": "Sarah", "min_duration": 30, "start": 105, "end": 600},   # 10:45 AM to 7:00 PM
        "Haight-Ashbury": {"person": "Richard", "min_duration": 90, "start": 165, "end": 405},  # 11:45 AM to 3:45 PM
        "Mission District": {"person": "Elizabeth", "min_duration": 120, "start": 120, "end": 495}, # 11:00 AM to 5:15 PM
        "Golden Gate Park": {"person": "Michelle", "min_duration": 90, "start": 555, "end": 705}   # 6:15 PM to 8:45 PM
    }
    
    # Define travel times (in minutes)
    travel_times = {
        'Richmond District': {
            'Sunset District': 11,
            'Haight-Ashbury': 10,
            'Mission District': 20,
            'Golden Gate Park': 9
        },
        'Sunset District': {
            'Richmond District': 12,
            'Haight-Ashbury': 15,
            'Mission District': 24,
            'Golden Gate Park': 11
        },
        'Haight-Ashbury': {
            'Richmond District': 10,
            'Sunset District': 15,
            'Mission District': 11,
            'Golden Gate Park': 7
        },
        'Mission District': {
            'Richmond District': 20,
            'Sunset District': 24,
            'Haight-Ashbury': 12,
            'Golden Gate Park': 17
        },
        'Golden Gate Park': {
            'Richmond District': 7,
            'Sunset District': 10,
            'Haight-Ashbury': 7,
            'Mission District': 17
        }
    }
    
    locations = list(constraints.keys())
    all_permutations = list(itertools.permutations(locations))
    
    best_schedule = []
    best_count = 0
    
    for perm in all_permutations:
        current_loc = 'Richmond District'
        current_time = 0
        schedule = []
        count = 0
        feasible = True
        
        for loc in perm:
            travel_duration = travel_times[current_loc][loc]
            current_time += travel_duration
            constr = constraints[loc]
            start_meeting = max(current_time, constr['start'])
            end_meeting = start_meeting + constr['min_duration']
            
            if end_meeting > constr['end']:
                feasible = False
                break
                
            schedule.append({
                'location': loc,
                'person': constr['person'],
                'start_time': start_meeting,
                'end_time': end_meeting
            })
            count += 1
            current_loc = loc
            current_time = end_meeting
        
        if count > best_count:
            best_count = count
            best_schedule = schedule
            if best_count == 4:
                break
    
    # Convert minutes to time strings (24-hour format)
    itinerary = []
    for event in best_schedule:
        start_total_minutes = 540 + event['start_time']  # 9:00 AM is 540 minutes from midnight
        end_total_minutes = 540 + event['end_time']
        
        start_h = start_total_minutes // 60
        start_m = start_total_minutes % 60
        end_h = end_total_minutes // 60
        end_m = end_total_minutes % 60
        
        start_str = f"{start_h}:{start_m:02d}"
        end_str = f"{end_h}:{end_m:02d}"
        
        itinerary.append({
            "action": "meet",
            "location": event['location'],
            "person": event['person'],
            "start_time": start_str,
            "end_time": end_str
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()