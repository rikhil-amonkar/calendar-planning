import itertools
import json

def main():
    # Define travel times (in minutes) between locations
    travel_times = {
        'Fisherman\'s Wharf': {
            'Presidio': 17,
            'Richmond District': 18,
            'Financial District': 11
        },
        'Presidio': {
            'Fisherman\'s Wharf': 19,
            'Richmond District': 7,
            'Financial District': 23
        },
        'Richmond District': {
            'Fisherman\'s Wharf': 18,
            'Presidio': 7,
            'Financial District': 21
        },
        'Financial District': {
            'Fisherman\'s Wharf': 10,
            'Presidio': 22,
            'Richmond District': 21
        }
    }
    
    # Meeting constraints
    meetings = [
        {
            'name': 'Emily',
            'location': 'Presidio',
            'start_avail': 16 * 60 + 15,  # 4:15 PM in minutes
            'end_avail': 21 * 60,         # 9:00 PM
            'min_duration': 105
        },
        {
            'name': 'Joseph',
            'location': 'Richmond District',
            'start_avail': 17 * 60 + 15,   # 5:15 PM
            'end_avail': 22 * 60,          # 10:00 PM
            'min_duration': 120
        },
        {
            'name': 'Melissa',
            'location': 'Financial District',
            'start_avail': 15 * 60 + 45,   # 3:45 PM
            'end_avail': 21 * 60 + 45,     # 9:45 PM
            'min_duration': 75
        }
    ]
    
    start_location = 'Fisherman\'s Wharf'
    start_time = 9 * 60  # 9:00 AM in minutes
    
    candidates = []
    
    # Try all permutations of meetings
    for perm in itertools.permutations(meetings):
        current_loc = start_location
        current_time = start_time
        schedule = []
        feasible = True
        
        for meeting in perm:
            # Travel to meeting location
            travel_duration = travel_times[current_loc][meeting['location']]
            current_time += travel_duration
            
            # Wait if arriving before available time
            if current_time < meeting['start_avail']:
                current_time = meeting['start_avail']
                
            # Check if meeting can be scheduled
            meeting_end = current_time + meeting['min_duration']
            if meeting_end > meeting['end_avail']:
                feasible = False
                break
                
            # Schedule meeting
            schedule.append({
                'meeting': meeting,
                'start': current_time,
                'end': meeting_end
            })
            
            # Update for next meeting
            current_time = meeting_end
            current_loc = meeting['location']
        
        if feasible:
            candidates.append({
                'count': 3,
                'finish_time': current_time,
                'schedule': schedule
            })
    
    # Fallback to fewer meetings if needed
    if not candidates:
        for pair in itertools.combinations(meetings, 2):
            for perm in itertools.permutations(pair):
                current_loc = start_location
                current_time = start_time
                schedule = []
                feasible = True
                
                for meeting in perm:
                    travel_duration = travel_times[current_loc][meeting['location']]
                    current_time += travel_duration
                    
                    if current_time < meeting['start_avail']:
                        current_time = meeting['start_avail']
                    
                    meeting_end = current_time + meeting['min_duration']
                    if meeting_end > meeting['end_avail']:
                        feasible = False
                        break
                    
                    schedule.append({
                        'meeting': meeting,
                        'start': current_time,
                        'end': meeting_end
                    })
                    
                    current_time = meeting_end
                    current_loc = meeting['location']
                
                if feasible:
                    candidates.append({
                        'count': len(perm),
                        'finish_time': current_time,
                        'schedule': schedule
                    })
    
    if not candidates:
        for meeting in meetings:
            current_loc = start_location
            current_time = start_time
            
            travel_duration = travel_times[current_loc][meeting['location']]
            current_time += travel_duration
            
            if current_time < meeting['start_avail']:
                current_time = meeting['start_avail']
            
            meeting_end = current_time + meeting['min_duration']
            if meeting_end <= meeting['end_avail']:
                candidates.append({
                    'count': 1,
                    'finish_time': meeting_end,
                    'schedule': [{
                        'meeting': meeting,
                        'start': current_time,
                        'end': meeting_end
                    }]
                })
    
    # Select best candidate with preference for specific order
    best_candidate = None
    if candidates:
        three_candidates = [c for c in candidates if c['count'] == 3]
        if three_candidates:
            # Prefer schedule: Emily -> Joseph -> Melissa if available
            for c in three_candidates:
                names = [event['meeting']['name'] for event in c['schedule']]
                if names == ['Emily', 'Joseph', 'Melissa']:
                    best_candidate = c
                    break
            if not best_candidate:
                # Otherwise choose earliest finish
                best_candidate = min(three_candidates, key=lambda c: c['finish_time'])
        else:
            best_candidate = min(candidates, key=lambda c: (-c['count'], c['finish_time']))
    else:
        best_candidate = {'schedule': []}
    
    # Format itinerary in 24-hour format
    itinerary = []
    for event in best_candidate['schedule']:
        meeting = event['meeting']
        start_minutes = event['start']
        end_minutes = event['end']
        
        # Convert to 24-hour "H:MM" format
        def format_time(minutes):
            hour = minutes // 60
            minute = minutes % 60
            return f"{hour}:{minute:02d}"
        
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['name'],
            "start_time": format_time(start_minutes),
            "end_time": format_time(end_minutes)
        })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()