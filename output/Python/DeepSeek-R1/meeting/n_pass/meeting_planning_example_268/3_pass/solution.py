import json
import itertools

def main():
    # Define travel times in minutes (corrected Alamo Square -> Russian Hill to 15)
    travel_time = {
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Presidio"): 18,
        ("Alamo Square", "Russian Hill"): 15,  # Corrected from 13 to 15
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14
    }
    
    # Friend constraints: name, location, start (minutes), end (minutes), min_duration
    friends = [
        {"name": "Timothy", "location": "Alamo Square", "start": 720, "end": 975, "min_duration": 105},
        {"name": "Mark", "location": "Presidio", "start": 1125, "end": 1260, "min_duration": 60},
        {"name": "Joseph", "location": "Russian Hill", "start": 1005, "end": 1290, "min_duration": 60}
    ]
    
    start_location = "Golden Gate Park"
    start_time = 540  # 9:00 in minutes
    
    best_candidate = None
    
    # Consider meeting 3, 2, or 1 friend (in that order)
    for r in range(len(friends), 0, -1):
        for perm in itertools.permutations(range(len(friends)), r):
            current_loc = start_location
            current_time = start_time
            total_waiting = 0
            meetings = []
            valid = True
            
            for idx in perm:
                friend = friends[idx]
                key = (current_loc, friend['location'])
                travel = travel_time[key]
                
                # Determine when we can leave current location
                leave_time = max(current_time, friend['start'] - travel)
                initial_wait = leave_time - current_time
                total_waiting += initial_wait
                
                arrival_time = leave_time + travel
                wait_at_location = max(0, friend['start'] - arrival_time)
                total_waiting += wait_at_location
                
                # Check waiting constraint immediately
                if total_waiting > 360:
                    valid = False
                    break
                
                start_meeting = max(arrival_time, friend['start'])
                end_meeting = start_meeting + friend['min_duration']
                
                # Check if meeting fits in friend's window
                if end_meeting > friend['end']:
                    valid = False
                    break
                
                meetings.append({
                    "friend": friend['name'],
                    "location": friend['location'],
                    "start": start_meeting,
                    "end": end_meeting
                })
                
                current_loc = friend['location']
                current_time = end_meeting
            
            # Only consider valid schedules within waiting limit
            if valid and total_waiting <= 360:
                candidate = {
                    "num_met": len(meetings),
                    "total_waiting": total_waiting,
                    "meetings": meetings
                }
                # Select candidate with most meetings, then least waiting
                if best_candidate is None:
                    best_candidate = candidate
                else:
                    if candidate['num_met'] > best_candidate['num_met']:
                        best_candidate = candidate
                    elif candidate['num_met'] == best_candidate['num_met']:
                        if candidate['total_waiting'] < best_candidate['total_waiting']:
                            best_candidate = candidate
    
    # If no valid schedule found, create empty itinerary
    if best_candidate is None:
        itinerary = []
    else:
        itinerary = []
        for meeting in best_candidate['meetings']:
            start_minutes = meeting['start']
            end_minutes = meeting['end']
            
            start_hour = start_minutes // 60
            start_minute = start_minutes % 60
            end_hour = end_minutes // 60
            end_minute = end_minutes % 60
            
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
            
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['friend'],
                "start_time": start_str,
                "end_time": end_str
            })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()