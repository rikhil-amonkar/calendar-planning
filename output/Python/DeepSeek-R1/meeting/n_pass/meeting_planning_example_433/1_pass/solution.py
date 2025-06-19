import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hour * 60 + minutes

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    travel_times = {
        'Nob Hill': {
            'Richmond District': 14,
            'Financial District': 9,
            'North Beach': 8,
            'The Castro': 17,
            'Golden Gate Park': 17
        },
        'Richmond District': {
            'Nob Hill': 17,
            'Financial District': 22,
            'North Beach': 17,
            'The Castro': 16,
            'Golden Gate Park': 9
        },
        'Financial District': {
            'Nob Hill': 8,
            'Richmond District': 21,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'North Beach': {
            'Nob Hill': 7,
            'Richmond District': 18,
            'Financial District': 8,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Nob Hill': 16,
            'Richmond District': 16,
            'Financial District': 20,
            'North Beach': 20,
            'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Nob Hill': 20,
            'Richmond District': 7,
            'Financial District': 26,
            'North Beach': 24,
            'The Castro': 13
        }
    }
    
    meetings = [
        ("Emily", "Richmond District", time_to_minutes("19:00"), time_to_minutes("21:00"), 15),
        ("Margaret", "Financial District", time_to_minutes("16:30"), time_to_minutes("20:15"), 75),
        ("Ronald", "North Beach", time_to_minutes("18:30"), time_to_minutes("19:30"), 45),
        ("Deborah", "The Castro", time_to_minutes("13:45"), time_to_minutes("21:15"), 90),
        ("Jeffrey", "Golden Gate Park", time_to_minutes("11:15"), time_to_minutes("14:30"), 120)
    ]
    
    start_time = time_to_minutes("9:00")
    start_location = "Nob Hill"
    
    best_itinerary = []
    best_count = 0
    
    for perm in itertools.permutations(meetings):
        current_time = start_time
        current_loc = start_location
        itinerary_perm = []
        
        for meeting in perm:
            person, loc, start_avail, end_avail, dur = meeting
            tt = travel_times[current_loc][loc]
            arrival = current_time + tt
            start_meeting = max(arrival, start_avail)
            if start_meeting + dur <= end_avail:
                itinerary_perm.append({
                    "person": person,
                    "location": loc,
                    "start": start_meeting,
                    "end": start_meeting + dur
                })
                current_time = start_meeting + dur
                current_loc = loc
            else:
                current_time = arrival
                current_loc = loc
        
        if len(itinerary_perm) > best_count:
            best_count = len(itinerary_perm)
            best_itinerary = itinerary_perm
    
    itinerary_sorted = sorted(best_itinerary, key=lambda x: x["start"])
    result = {
        "itinerary": [
            {
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": minutes_to_time(item["start"]),
                "end_time": minutes_to_time(item["end"])
            } for item in itinerary_sorted
        ]
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()