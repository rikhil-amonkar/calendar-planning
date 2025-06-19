import itertools
import json

def main():
    # Define travel times between locations
    travel_times = {
        "Haight-Ashbury": {
            "Fisherman's Wharf": 23,
            "Richmond District": 10,
            "Mission District": 11,
            "Bayview": 18
        },
        "Fisherman's Wharf": {
            "Haight-Ashbury": 22,
            "Richmond District": 18,
            "Mission District": 22,
            "Bayview": 26
        },
        "Richmond District": {
            "Haight-Ashbury": 10,
            "Fisherman's Wharf": 18,
            "Mission District": 20,
            "Bayview": 26
        },
        "Mission District": {
            "Haight-Ashbury": 12,
            "Fisherman's Wharf": 22,
            "Richmond District": 20,
            "Bayview": 15
        },
        "Bayview": {
            "Haight-Ashbury": 19,
            "Fisherman's Wharf": 25,
            "Richmond District": 25,
            "Mission District": 13
        }
    }
    
    # Define meetings with constraints (times in minutes from midnight)
    meetings = [
        {
            'person': 'Sarah',
            'location': "Fisherman's Wharf",
            'start_avail': 14 * 60 + 45,  # 14:45
            'end_avail': 17 * 60 + 30,    # 17:30
            'min_dur': 105
        },
        {
            'person': 'Mary',
            'location': "Richmond District",
            'start_avail': 13 * 60,       # 13:00
            'end_avail': 19 * 60 + 15,    # 19:15
            'min_dur': 75
        },
        {
            'person': 'Helen',
            'location': "Mission District",
            'start_avail': 21 * 60 + 45,  # 21:45
            'end_avail': 22 * 60 + 30,    # 22:30
            'min_dur': 30
        },
        {
            'person': 'Thomas',
            'location': "Bayview",
            'start_avail': 15 * 60 + 15,  # 15:15
            'end_avail': 18 * 60 + 45,    # 18:45
            'min_dur': 120
        }
    ]
    
    # Initial conditions
    start_time = 9 * 60  # 9:00 AM in minutes
    start_location = "Haight-Ashbury"
    best_itinerary = []
    found = False
    
    # Try subsets from largest (size 4) to smallest (size 1)
    n = len(meetings)
    for k in range(n, 0, -1):
        for subset in itertools.combinations(meetings, k):
            for perm in itertools.permutations(subset):
                current_time = start_time
                current_location = start_location
                itinerary = []
                feasible = True
                
                for meeting in perm:
                    loc = meeting['location']
                    # Get travel time
                    travel = travel_times[current_location][loc]
                    current_time += travel  # arrival time at meeting location
                    
                    # Calculate meeting start time
                    start_meeting = max(current_time, meeting['start_avail'])
                    end_meeting = start_meeting + meeting['min_dur']
                    
                    # Check if meeting fits within availability
                    if end_meeting > meeting['end_avail']:
                        feasible = False
                        break
                    
                    # Add meeting to itinerary
                    itinerary.append({
                        'person': meeting['person'],
                        'location': loc,
                        'start_time': start_meeting,
                        'end_time': end_meeting
                    })
                    
                    current_time = end_meeting
                    current_location = loc
                
                if feasible:
                    best_itinerary = itinerary
                    found = True
                    break
            if found:
                break
        if found:
            break
    
    # Convert itinerary to output format
    output_itinerary = []
    for event in best_itinerary:
        # Format start time
        start_minutes = event['start_time']
        start_hour = start_minutes // 60
        start_min = start_minutes % 60
        start_str = f"{start_hour}:{start_min:02d}"
        
        # Format end time
        end_minutes = event['end_time']
        end_hour = end_minutes // 60
        end_min = end_minutes % 60
        end_str = f"{end_hour}:{end_min:02d}"
        
        output_itinerary.append({
            "action": "meet",
            "location": event['location'],
            "person": event['person'],
            "start_time": start_str,
            "end_time": end_str
        })
    
    # Output as JSON
    result = {"itinerary": output_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()