import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Alamo Square"): 17,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Financial District"): 17,
}

# Define meeting constraints
arrival_time = datetime.strptime("9:00", "%H:%M")
stephanie_start = datetime.strptime("8:15", "%H:%M")
stephanie_end = datetime.strptime("11:30", "%H:%M")
john_start = datetime.strptime("10:15", "%H:%M")
john_end = datetime.strptime("20:45", "%H:%M")

stephanie_meeting_time = 90  # minutes
john_meeting_time = 30  # minutes

# Initialize itinerary
itinerary = []

# Helper function to format time
def format_time(dt):
    return dt.strftime("%H:%M")

# Function to schedule meetings
def schedule_meetings():
    global itinerary
    # Meeting with Stephanie
    start_time = arrival_time + timedelta(minutes=travel_times[("Embarcadero", "Financial District")])
    
    if start_time < stephanie_start:
        start_time = stephanie_start

    end_time = start_time + timedelta(minutes=stephanie_meeting_time)
    
    if end_time > stephanie_end:
        end_time = stephanie_end

    if end_time - start_time >= timedelta(minutes=stephanie_meeting_time):
        itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Stephanie",
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
        
        # Travel to John
        travel_to_john = end_time + timedelta(minutes=travel_times[("Financial District", "Alamo Square")])
        
        # Meeting with John
        john_meeting_start = max(travel_to_john, john_start)
        john_meeting_end = john_meeting_start + timedelta(minutes=john_meeting_time)

        if john_meeting_end <= john_end:
            itinerary.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "John",
                "start_time": format_time(john_meeting_start),
                "end_time": format_time(john_meeting_end)
            })

schedule_meetings()

# Output the result in JSON format
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))