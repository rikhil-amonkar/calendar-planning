import json

def get_travel_time(from_loc, to_loc):
    if from_loc == "Financial District" and to_loc == "Chinatown":
        return 5
    elif from_loc == "Financial District" and to_loc == "Golden Gate Park":
        return 23
    elif from_loc == "Chinatown" and to_loc == "Golden Gate Park":
        return 23
    elif from_loc == "Golden Gate Park" and to_loc == "Chinatown":
        return 23
    elif from_loc == "Chinatown" and to_loc == "Financial District":
        return 5
    elif from_loc == "Golden Gate Park" and to_loc == "Financial District":
        return 26
    else:
        return 0

def format_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def schedule_order(order, start_time_financial=540):
    first, second = order[0], order[1]
    travel_FA = get_travel_time("Financial District", first['location'])
    travel_AB = get_travel_time(first['location'], second['location'])
    
    # Try backward scheduling for the second meeting
    T2 = second['available_start']
    end_A = T2 - travel_AB
    start_A = end_A - first['duration']
    departure = start_A - travel_FA
    
    if (departure >= start_time_financial and
        start_A >= first['available_start'] and
        end_A <= first['available_end'] and
        T2 + second['duration'] <= second['available_end']):
        meetings = [
            {"person": first['person'], "location": first['location'], "start": start_A, "end": end_A},
            {"person": second['person'], "location": second['location'], "start": T2, "end": T2 + second['duration']}
        ]
        return meetings, T2 + second['duration']
    
    # Forward scheduling
    arrival1 = start_time_financial + travel_FA
    start1 = max(arrival1, first['available_start'])
    end1 = start1 + first['duration']
    if end1 > first['available_end']:
        return None, None
        
    arrival2 = end1 + travel_AB
    start2 = max(arrival2, second['available_start'])
    end2 = start2 + second['duration']
    if end2 > second['available_end']:
        return None, None
        
    meetings = [
        {"person": first['person'], "location": first['location'], "start": start1, "end": end1},
        {"person": second['person'], "location": second['location'], "start": start2, "end": end2}
    ]
    return meetings, end2

def main():
    start_time_financial = 540  # 9:00 AM in minutes
    orders = [
        [  # Order 1: Barbara then Kenneth
            {"person": "Barbara", "location": "Golden Gate Park", "duration": 45, "available_start": 495, "available_end": 1140},
            {"person": "Kenneth", "location": "Chinatown", "duration": 90, "available_start": 720, "available_end": 900}
        ],
        [  # Order 2: Kenneth then Barbara
            {"person": "Kenneth", "location": "Chinatown", "duration": 90, "available_start": 720, "available_end": 900},
            {"person": "Barbara", "location": "Golden Gate Park", "duration": 45, "available_start": 495, "available_end": 1140}
        ]
    ]
    
    best_end_time = None
    best_schedule = None
    
    for order in orders:
        meetings, end_time = schedule_order(order, start_time_financial)
        if meetings is not None:
            if best_end_time is None or end_time < best_end_time:
                best_end_time = end_time
                best_schedule = meetings
    
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": format_minutes(meeting['start']),
            "end_time": format_minutes(meeting['end'])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()