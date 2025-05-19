import json
from datetime import datetime, timedelta

# Constants
TRAVEL_TIMES = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Chinatown"): 20,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Chinatown"): 16,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Union Square"): 7,
}

# Meeting constraints
constraints = {
    "Emily": {
        "location": "Alamo Square",
        "start_time": "11:45",
        "end_time": "15:15",
        "min_duration": 105,
    },
    "Barbara": {
        "location": "Union Square",
        "start_time": "16:45",
        "end_time": "18:15",
        "min_duration": 60,
    },
    "William": {
        "location": "Chinatown",
        "start_time": "17:15",
        "end_time": "19:00",
        "min_duration": 105,
    },
}

def time_to_minutes(t):
    """Convert 'HH:MM' time format to minutes since 00:00."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since 00:00 back to 'HH:MM' format."""
    h, m = divmod(m, 60)
    return f"{h}:{m:02d}"

# Meeting schedule computation
def compute_schedule():
    start_time = time_to_minutes("09:00")
    itinerary = []
    
    # Meeting Emily
    emily_start = time_to_minutes(constraints["Emily"]["start_time"])
    emily_end = time_to_minutes(constraints["Emily"]["end_time"])

    # Time after traveling from Castro to Alamo Square
    travel_to_emily = TRAVEL_TIMES[("The Castro", "Alamo Square")]
    travel_to_emily_end_time = start_time + travel_to_emily
    
    if travel_to_emily_end_time <= emily_end:
        meeting_time_with_emily = max(emily_start, travel_to_emily_end_time)
        emily_meeting_end = meeting_time_with_emily + constraints["Emily"]["min_duration"]
        
        if emily_meeting_end <= emily_end:
            itinerary.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "Emily",
                "start_time": minutes_to_time(meeting_time_with_emily),
                "end_time": minutes_to_time(emily_meeting_end),
            })
    
            # Travel to Union Square
            travel_to_barbara = TRAVEL_TIMES[("Alamo Square", "Union Square")]
            travel_to_barbara_end_time = emily_meeting_end + travel_to_barbara
            
            # Meeting Barbara
            barbara_start = time_to_minutes(constraints["Barbara"]["start_time"])
            barbara_end = time_to_minutes(constraints["Barbara"]["end_time"])

            if travel_to_barbara_end_time <= barbara_end:
                meeting_time_with_barbara = max(barbara_start, travel_to_barbara_end_time)
                barbara_meeting_end = meeting_time_with_barbara + constraints["Barbara"]["min_duration"]
                
                if barbara_meeting_end <= barbara_end:
                    itinerary.append({
                        "action": "meet",
                        "location": "Union Square",
                        "person": "Barbara",
                        "start_time": minutes_to_time(meeting_time_with_barbara),
                        "end_time": minutes_to_time(barbara_meeting_end),
                    })

                    # Travel to Chinatown
                    travel_to_william = TRAVEL_TIMES[("Union Square", "Chinatown")]
                    travel_to_william_end_time = barbara_meeting_end + travel_to_william
                    
                    # Meeting William
                    william_start = time_to_minutes(constraints["William"]["start_time"])
                    william_end = time_to_minutes(constraints["William"]["end_time"])

                    if travel_to_william_end_time <= william_end:
                        meeting_time_with_william = max(william_start, travel_to_william_end_time)
                        william_meeting_end = meeting_time_with_william + constraints["William"]["min_duration"]
                        
                        if william_meeting_end <= william_end:
                            itinerary.append({
                                "action": "meet",
                                "location": "Chinatown",
                                "person": "William",
                                "start_time": minutes_to_time(meeting_time_with_william),
                                "end_time": minutes_to_time(william_meeting_end),
                            })

    return {"itinerary": itinerary}

# Generating the meeting schedule
schedule = compute_schedule()

# Print the output as JSON
print(json.dumps(schedule, indent=2))