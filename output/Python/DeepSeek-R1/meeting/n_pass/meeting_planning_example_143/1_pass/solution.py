import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minutes = int(parts[1])
    return hour * 60 + minutes

def minutes_to_time(minutes_val):
    hour = minutes_val // 60
    minute = minutes_val % 60
    return f"{hour}:{minute:02d}"

def main():
    travel_times = {
        "North Beach": {
            "Pacific Heights": 8,
            "Embarcadero": 6
        },
        "Pacific Heights": {
            "North Beach": 9,
            "Embarcadero": 10
        },
        "Embarcadero": {
            "North Beach": 5,
            "Pacific Heights": 11
        }
    }
    
    start_location = "North Beach"
    start_time_str = "9:00"
    start_time = time_to_minutes(start_time_str)
    
    mark_location = "Embarcadero"
    mark_available_start_str = "13:00"
    mark_available_end_str = "17:45"
    mark_min_duration = 120
    
    karen_location = "Pacific Heights"
    karen_available_start_str = "18:45"
    karen_available_end_str = "20:15"
    karen_min_duration = 90
    
    mark_start = time_to_minutes(mark_available_start_str)
    mark_end = time_to_minutes(mark_available_end_str)
    karen_start = time_to_minutes(karen_available_start_str)
    karen_end = time_to_minutes(karen_available_end_str)
    
    travel_to_mark = travel_times[start_location][mark_location]
    earliest_arrival_at_mark = start_time + travel_to_mark
    
    mark_meeting_start = min(mark_end - mark_min_duration, max(earliest_arrival_at_mark, mark_start))
    mark_meeting_end = mark_meeting_start + mark_min_duration
    
    travel_to_karen = travel_times[mark_location][karen_location]
    arrival_at_karen = mark_meeting_end + travel_to_karen
    
    karen_meeting_start = max(arrival_at_karen, karen_start)
    if karen_meeting_start + karen_min_duration > karen_end:
        karen_meeting_start = None
    else:
        karen_meeting_end = karen_meeting_start + karen_min_duration
    
    itinerary = []
    if mark_meeting_start is not None:
        itinerary.append({
            "action": "meet",
            "location": mark_location,
            "person": "Mark",
            "start_time": minutes_to_time(mark_meeting_start),
            "end_time": minutes_to_time(mark_meeting_end)
        })
    
    if karen_meeting_start is not None:
        itinerary.append({
            "action": "meet",
            "location": karen_location,
            "person": "Karen",
            "start_time": minutes_to_time(karen_meeting_start),
            "end_time": minutes_to_time(karen_meeting_end)
        })
    
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()