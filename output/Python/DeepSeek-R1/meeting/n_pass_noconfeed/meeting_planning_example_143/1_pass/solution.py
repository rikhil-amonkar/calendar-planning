import json

def to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02}"

def main():
    travel_times = {
        'North Beach': {'Pacific Heights': 8, 'Embarcadero': 6},
        'Pacific Heights': {'North Beach': 9, 'Embarcadero': 10},
        'Embarcadero': {'North Beach': 5, 'Pacific Heights': 11}
    }
    
    start_time_str = "9:00"
    karen_window = ["18:45", "20:15"]
    mark_window = ["13:00", "17:45"]
    min_karen = 90
    min_mark = 120

    start_time = to_minutes(start_time_str)
    karen_start_avail = to_minutes(karen_window[0])
    karen_end_avail = to_minutes(karen_window[1])
    mark_start_avail = to_minutes(mark_window[0])
    mark_end_avail = to_minutes(mark_window[1])

    # Calculate meeting for Mark in the context of meeting both
    travel_NB_to_Emb = travel_times['North Beach']['Embarcadero']
    leave_NB_time = max(start_time, mark_start_avail - travel_NB_to_Emb)
    arrival_Emb = leave_NB_time + travel_NB_to_Emb
    mark_meeting_start = max(arrival_Emb, mark_start_avail)
    travel_Emb_to_PH = travel_times['Embarcadero']['Pacific Heights']
    latest_leave_Emb = karen_start_avail - travel_Emb_to_PH
    mark_meeting_end_both = min(mark_end_avail, latest_leave_Emb)
    mark_duration_both = mark_meeting_end_both - mark_meeting_start

    if mark_duration_both >= min_mark:
        itinerary = [
            {
                "action": "meet",
                "location": "Embarcadero",
                "person": "Mark",
                "start_time": format_time(mark_meeting_start),
                "end_time": format_time(mark_meeting_end_both)
            },
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Karen",
                "start_time": format_time(karen_start_avail),
                "end_time": format_time(karen_end_avail)
            }
        ]
    else:
        mark_meeting_end_alone = mark_end_avail
        mark_duration_alone = mark_meeting_end_alone - mark_meeting_start
        if mark_duration_alone >= min_mark:
            itinerary = [
                {
                    "action": "meet",
                    "location": "Embarcadero",
                    "person": "Mark",
                    "start_time": format_time(mark_meeting_start),
                    "end_time": format_time(mark_meeting_end_alone)
                }
            ]
        else:
            travel_NB_to_PH = travel_times['North Beach']['Pacific Heights']
            leave_NB_time_k = max(start_time, karen_start_avail - travel_NB_to_PH)
            arrival_PH = leave_NB_time_k + travel_NB_to_PH
            karen_meeting_start = max(arrival_PH, karen_start_avail)
            karen_meeting_end = karen_end_avail
            karen_duration = karen_meeting_end - karen_meeting_start
            if karen_duration >= min_karen:
                itinerary = [
                    {
                        "action": "meet",
                        "location": "Pacific Heights",
                        "person": "Karen",
                        "start_time": format_time(karen_meeting_start),
                        "end_time": format_time(karen_meeting_end)
                    }
                ]
            else:
                itinerary = []

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()