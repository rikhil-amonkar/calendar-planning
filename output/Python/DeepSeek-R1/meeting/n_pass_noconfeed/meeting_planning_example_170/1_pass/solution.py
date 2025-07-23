import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        "North Beach": {
            "Union Square": 7,
            "Russian Hill": 4
        },
        "Union Square": {
            "North Beach": 10,
            "Russian Hill": 13
        },
        "Russian Hill": {
            "North Beach": 5,
            "Union Square": 11
        }
    }
    
    meetings = [
        {
            "person": "Emily",
            "location": "Union Square",
            "available_start": "16:00",
            "available_end": "17:15",
            "min_duration": 45
        },
        {
            "person": "Margaret",
            "location": "Russian Hill",
            "available_start": "19:00",
            "available_end": "21:00",
            "min_duration": 120
        }
    ]
    
    start_time_minutes = time_to_minutes("9:00")
    start_location = "North Beach"
    
    best_itinerary = None
    best_count = 0
    best_total_time = 0
    
    for order in itertools.permutations(meetings):
        current_time = start_time_minutes
        current_location = start_location
        scheduled = []
        feasible = True
        total_meeting_time = 0
        
        for meeting in order:
            if current_location != meeting['location']:
                travel_time = travel_times[current_location][meeting['location']]
                current_time += travel_time
            else:
                travel_time = 0
            
            avail_start = time_to_minutes(meeting['available_start'])
            avail_end = time_to_minutes(meeting['available_end'])
            min_duration = meeting['min_duration']
            
            start_meeting = max(current_time, avail_start)
            if start_meeting + min_duration > avail_end:
                feasible = False
                break
            
            end_meeting = avail_end
            scheduled.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(end_meeting)
            })
            total_meeting_time += (end_meeting - start_meeting)
            
            current_time = end_meeting
            current_location = meeting['location']
        
        if feasible:
            count = len(scheduled)
            if count > best_count or (count == best_count and total_meeting_time > best_total_time):
                best_count = count
                best_total_time = total_meeting_time
                best_itinerary = scheduled
    
    if best_itinerary is None:
        best_itinerary = []
    
    result = {
        "itinerary": best_itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()