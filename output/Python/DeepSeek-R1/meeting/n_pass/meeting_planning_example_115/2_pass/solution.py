import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

def main():
    start_time_str = "9:00"
    start_minutes = time_to_minutes(start_time_str)
    
    travel_times = {
        ('Richmond District', 'Marina District'): 9,
        ('Marina District', 'Pacific Heights'): 7
    }
    # Add travel time from Richmond to Pacific Heights (via Marina)
    travel_times[('Richmond District', 'Pacific Heights')] = travel_times[('Richmond District', 'Marina District')] + travel_times[('Marina District', 'Pacific Heights')]
    
    carol_avail_start = time_to_minutes("11:30")
    carol_avail_end = time_to_minutes("15:00")
    carol_duration = 60
    
    jessica_avail_start = time_to_minutes("15:30")
    jessica_avail_end = time_to_minutes("16:45")
    jessica_duration = 45
    
    # Try to schedule both meetings
    itinerary = []
    
    # Schedule Carol as early as possible
    carol_start = max(start_minutes + travel_times[('Richmond District', 'Marina District')], carol_avail_start)
    if carol_start + carol_duration > carol_avail_end:
        carol_possible = False
    else:
        carol_possible = True
        carol_end = carol_start + carol_duration
        
        # Travel to Pacific Heights for Jessica
        arrival_pacific = carol_end + travel_times[('Marina District', 'Pacific Heights')]
        jessica_start = max(arrival_pacific, jessica_avail_start)
        if jessica_start + jessica_duration <= jessica_avail_end:
            # Both meetings can be scheduled
            itinerary = [
                {
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Carol",
                    "start_time": minutes_to_time(carol_start),
                    "end_time": minutes_to_time(carol_end)
                },
                {
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Jessica",
                    "start_time": minutes_to_time(jessica_start),
                    "end_time": minutes_to_time(jessica_start + jessica_duration)
                }
            ]
        else:
            # Can schedule Carol but not Jessica
            itinerary = [
                {
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Carol",
                    "start_time": minutes_to_time(carol_start),
                    "end_time": minutes_to_time(carol_end)
                }
            ]
    
    # If couldn't schedule both, try single meetings
    if not itinerary:
        carol_possible = False
        jessica_possible = False
        
        # Check if Carol can be scheduled alone
        carol_start = max(start_minutes + travel_times[('Richmond District', 'Marina District')], carol_avail_start)
        if carol_start + carol_duration <= carol_avail_end:
            carol_possible = True
        
        # Check if Jessica can be scheduled alone
        jessica_start = max(start_minutes + travel_times[('Richmond District', 'Pacific Heights')], jessica_avail_start)
        if jessica_start + jessica_duration <= jessica_avail_end:
            jessica_possible = True
        
        # Create itinerary based on possible meetings
        if carol_possible and jessica_possible:
            # Shouldn't happen since we already tried both, but included for completeness
            itinerary = [
                {
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Carol",
                    "start_time": minutes_to_time(carol_start),
                    "end_time": minutes_to_time(carol_start + carol_duration)
                }
            ]
        elif carol_possible:
            itinerary = [
                {
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Carol",
                    "start_time": minutes_to_time(carol_start),
                    "end_time": minutes_to_time(carol_start + carol_duration)
                }
            ]
        elif jessica_possible:
            itinerary = [
                {
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Jessica",
                    "start_time": minutes_to_time(jessica_start),
                    "end_time": minutes_to_time(jessica_start + jessica_duration)
                }
            ]
        else:
            itinerary = []
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()