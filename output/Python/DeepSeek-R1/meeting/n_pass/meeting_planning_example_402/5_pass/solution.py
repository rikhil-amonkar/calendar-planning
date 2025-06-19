import json

def format_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    mins = total_minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Sunset District": 10,
            "Marina District": 16,
            "Financial District": 26,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Golden Gate Park": 7,
            "Sunset District": 15,
            "Marina District": 17,
            "Financial District": 21,
            "Union Square": 17
        },
        "Sunset District": {
            "Golden Gate Park": 11,
            "Haight-Ashbury": 15,
            "Marina District": 21,
            "Financial District": 31,
            "Union Square": 30
        },
        "Marina District": {
            "Golden Gate Park": 16,
            "Haight-Ashbury": 16,
            "Sunset District": 19,
            "Financial District": 17,
            "Union Square": 18
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Sunset District": 31,
            "Marina District": 15,
            "Union Square": 9
        },
        "Union Square": {
            "Golden Gate Park": 22,
            "Haight-Ashbury": 18,
            "Sunset District": 26,
            "Marina District": 18,
            "Financial District": 9
        }
    }
    
    meetings = [
        {"name": "Matthew", "location": "Marina District", "start_avail": 15, "end_avail": 120, "min_dur": 15},
        {"name": "Robert", "location": "Union Square", "start_avail": 75, "end_avail": 585, "min_dur": 15},
        {"name": "Joseph", "location": "Financial District", "start_avail": 135, "end_avail": 465, "min_dur": 30},
        {"name": "Patricia", "location": "Sunset District", "start_avail": 480, "end_avail": 645, "min_dur": 45},
        {"name": "Sarah", "location": "Haight-Ashbury", "start_avail": 480, "end_avail": 750, "min_dur": 105}
    ]
    
    current_location = "Golden Gate Park"
    current_time = 0
    itinerary = []
    
    for meeting in meetings:
        location = meeting["location"]
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        if arrival_time > meeting["end_avail"]:
            continue
            
        start_time = max(arrival_time, meeting["start_avail"])
        end_time = start_time + meeting["min_dur"]
        
        if end_time > 660:
            continue
            
        if end_time <= meeting["end_avail"]:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": meeting["name"],
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
            current_location = location
            current_time = end_time
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()