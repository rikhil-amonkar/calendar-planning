import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Richmond District", "Bayview"): 26,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Richmond District"): 18,
}

# Meeting constraints
meetings = {
    "Jessica": {"location": "Embarcadero", "start": "16:45", "end": "19:00", "duration": 30},
    "Sandra": {"location": "Richmond District", "start": "18:30", "end": "21:45", "duration": 120},
    "Jason": {"location": "Fisherman's Wharf", "start": "16:00", "end": "16:45", "duration": 30},
}

# Start time upon arrival at Bayview
arrival_time = datetime.strptime("09:00", "%H:%M")
schedule = []

def can_schedule_meeting(start_time, end_time):
    return start_time >= arrival_time and end_time <= datetime.strptime("21:45", "%H:%M")

# Schedule meetings
def schedule_meetings():
    global arrival_time
    
    # Meeting with Jason first
    jason_start = datetime.strptime(meetings["Jason"]["start"], "%H:%M")
    jason_end = jason_start + timedelta(minutes=meetings["Jason"]["duration"])
    travel_time_to_jason = travel_times[("Bayview", "Fisherman's Wharf")]
    
    if can_schedule_meeting(jason_start, jason_end):
        schedule.append({
            "action": "meet",
            "location": "Fisherman's Wharf",
            "person": "Jason",
            "start_time": jason_start.strftime("%H:%M"),
            "end_time": jason_end.strftime("%H:%M")
        })
        arrival_time = jason_end + timedelta(minutes=travel_times[("Fisherman's Wharf", "Embarcadero")])
        
        # Meeting with Jessica next
        jessica_start = max(arrival_time, datetime.strptime(meetings["Jessica"]["start"], "%H:%M"))
        jessica_end = jessica_start + timedelta(minutes=meetings["Jessica"]["duration"])
        
        travel_time_to_jessica = travel_times[("Fisherman's Wharf", "Embarcadero")]
        
        if jessica_start + timedelta(minutes=travel_time_to_jessica) <= datetime.strptime(meetings["Jessica"]["end"], "%H:%M"):
            arrival_time = jessica_start + timedelta(minutes=travel_time_to_jessica)
            schedule.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Jessica",
                "start_time": jessica_start.strftime("%H:%M"),
                "end_time": jessica_end.strftime("%H:%M")
            })
            arrival_time = jessica_end + timedelta(minutes=travel_times[("Embarcadero", "Richmond District")])
            
            # Meeting with Sandra next
            sandra_start = max(arrival_time, datetime.strptime(meetings["Sandra"]["start"], "%H:%M"))
            sandra_end = sandra_start + timedelta(minutes=meetings["Sandra"]["duration"])
            
            travel_time_to_sandra = travel_times[("Richmond District", "Bayview")]
            
            if sandra_start + timedelta(minutes=travel_time_to_sandra) <= datetime.strptime(meetings["Sandra"]["end"], "%H:%M"):
                schedule.append({
                    "action": "meet",
                    "location": "Richmond District",
                    "person": "Sandra",
                    "start_time": sandra_start.strftime("%H:%M"),
                    "end_time": sandra_end.strftime("%H:%M")
                })

schedule_meetings()

# JSON formatted output
output = {"itinerary": schedule}
print(json.dumps(output, indent=2))