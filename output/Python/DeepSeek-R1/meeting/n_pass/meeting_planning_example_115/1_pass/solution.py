import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02}"

def main():
    start_time_str = "9:00"
    start_minutes = time_to_minutes(start_time_str)
    
    travel_times = {
        ('Richmond District', 'Marina District'): 9,
        ('Marina District', 'Pacific Heights'): 7
    }
    
    carol_avail_start = time_to_minutes("11:30")
    carol_avail_end = time_to_minutes("15:00")
    carol_duration = 60
    
    jessica_avail_start = time_to_minutes("15:30")
    jessica_avail_end = time_to_minutes("16:45")
    jessica_duration = 45
    
    carol_start_max = carol_avail_end - carol_duration
    carol_start = carol_start_max
    
    leave_richmond = carol_start - travel_times[('Richmond District', 'Marina District')]
    if leave_richmond < start_minutes:
        carol_start = None
    else:
        arrival_marina = carol_start
        leave_marina = carol_start + carol_duration
        arrival_pacific = leave_marina + travel_times[('Marina District', 'Pacific Heights')]
        jessica_start = max(arrival_pacific, jessica_avail_start)
        if jessica_start + jessica_duration > jessica_avail_end:
            carol_start = None
    
    if carol_start is not None:
        carol_meeting_end = carol_start + carol_duration
        arrival_pacific = carol_meeting_end + travel_times[('Marina District', 'Pacific Heights')]
        jessica_start = max(arrival_pacific, jessica_avail_start)
        jessica_meeting_end = jessica_start + jessica_duration
        
        itinerary = [
            {
                "action": "meet",
                "location": "Marina District",
                "person": "Carol",
                "start_time": minutes_to_time(carol_start),
                "end_time": minutes_to_time(carol_meeting_end)
            },
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Jessica",
                "start_time": minutes_to_time(jessica_start),
                "end_time": minutes_to_time(jessica_meeting_end)
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        carol_possible = False
        jessica_possible = False
        carol_meeting = None
        jessica_meeting = None
        
        if carol_avail_end - carol_duration >= carol_avail_start:
            carol_start_candidate = carol_avail_end - carol_duration
            leave_richmond = carol_start_candidate - travel_times[('Richmond District', 'Marina District')]
            if leave_richmond >= start_minutes:
                carol_possible = True
                carol_meeting = {
                    'start': carol_start_candidate,
                    'end': carol_start_candidate + carol_duration
                }
        
        leave_richmond_j = jessica_avail_start - travel_times[('Richmond District', 'Pacific Heights')]
        if leave_richmond_j >= start_minutes:
            jessica_possible = True
            jessica_meeting = {
                'start': jessica_avail_start,
                'end': jessica_avail_start + jessica_duration
            }
        
        if carol_possible and jessica_possible:
            itinerary = [
                {
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Carol",
                    "start_time": minutes_to_time(carol_meeting['start']),
                    "end_time": minutes_to_time(carol_meeting['end'])
                }
            ]
            result = {"itinerary": itinerary}
            print(json.dumps(result))
        elif carol_possible:
            itinerary = [
                {
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Carol",
                    "start_time": minutes_to_time(carol_meeting['start']),
                    "end_time": minutes_to_time(carol_meeting['end'])
                }
            ]
            result = {"itinerary": itinerary}
            print(json.dumps(result))
        elif jessica_possible:
            itinerary = [
                {
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Jessica",
                    "start_time": minutes_to_time(jessica_meeting['start']),
                    "end_time": minutes_to_time(jessica_meeting['end'])
                }
            ]
            result = {"itinerary": itinerary}
            print(json.dumps(result))
        else:
            result = {"itinerary": []}
            print(json.dumps(result))

if __name__ == "__main__":
    main()