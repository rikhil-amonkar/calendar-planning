import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%-H:%M')

def calculate_schedule():
    # Input parameters
    current_location = "Bayview"
    current_time = parse_time("9:00")
    
    # Friends' availability
    friends = [
        {
            "name": "Betty",
            "location": "Embarcadero",
            "start": parse_time("19:45"),
            "end": parse_time("21:45"),
            "duration": timedelta(minutes=15)
        },
        {
            "name": "Karen",
            "location": "Fisherman's Wharf",
            "start": parse_time("8:45"),
            "end": parse_time("15:00"),
            "duration": timedelta(minutes=30)
        },
        {
            "name": "Anthony",
            "location": "Financial District",
            "start": parse_time("9:15"),
            "end": parse_time("21:30"),
            "duration": timedelta(minutes=105)
        }
    ]
    
    # Travel times matrix
    travel_times = {
        "Bayview": {
            "Embarcadero": timedelta(minutes=19),
            "Fisherman's Wharf": timedelta(minutes=25),
            "Financial District": timedelta(minutes=19)
        },
        "Embarcadero": {
            "Bayview": timedelta(minutes=21),
            "Fisherman's Wharf": timedelta(minutes=6),
            "Financial District": timedelta(minutes=5)
        },
        "Fisherman's Wharf": {
            "Bayview": timedelta(minutes=26),
            "Embarcadero": timedelta(minutes=8),
            "Financial District": timedelta(minutes=11)
        },
        "Financial District": {
            "Bayview": timedelta(minutes=19),
            "Embarcadero": timedelta(minutes=4),
            "Fisherman's Wharf": timedelta(minutes=10)
        }
    }
    
    itinerary = []
    
    # Helper function to find best meeting time
    def find_best_meeting(current_loc, current_t, friend):
        location = friend["location"]
        travel_time = travel_times[current_loc][location]
        arrival_time = current_t + travel_time
        
        # Determine meeting window
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["duration"]
        
        if meeting_end <= friend["end"]:
            return {
                "start": meeting_start,
                "end": meeting_end,
                "travel_time": travel_time
            }
        return None
    
    # Try different orders to maximize meetings
    meeting_orders = [
        ["Karen", "Anthony", "Betty"],
        ["Anthony", "Karen", "Betty"],
        ["Karen", "Betty", "Anthony"],
        ["Anthony", "Betty", "Karen"],
        ["Betty", "Karen", "Anthony"],
        ["Betty", "Anthony", "Karen"]
    ]
    
    best_itinerary = []
    max_meetings = 0
    
    for order in meeting_orders:
        temp_itinerary = []
        temp_location = current_location
        temp_time = current_time
        meetings = 0
        
        for name in order:
            friend = next(f for f in friends if f["name"] == name)
            meeting = find_best_meeting(temp_location, temp_time, friend)
            if meeting:
                temp_itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": format_time(meeting["start"]),
                    "end_time": format_time(meeting["end"])
                })
                temp_location = friend["location"]
                temp_time = meeting["end"]
                meetings += 1
        
        if meetings > max_meetings:
            max_meetings = meetings
            best_itinerary = temp_itinerary
        elif meetings == max_meetings and meetings > 0:
            # Prefer longer total meeting time
            current_total = sum((parse_time(i["end_time"]) - parse_time(i["start_time"])).total_seconds() for i in best_itinerary)
            new_total = sum((parse_time(i["end_time"]) - parse_time(i["start_time"])).total_seconds() for i in temp_itinerary)
            if new_total > current_total:
                best_itinerary = temp_itinerary
    
    return {"itinerary": best_itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))