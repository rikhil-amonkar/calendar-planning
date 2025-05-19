import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Mission District"): 26,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    ("Bayview", "Chinatown"): 22,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Mission District"): 13,
    ("Chinatown", "North Beach"): 6,
    ("Chinatown", "Mission District"): 18,
    ("North Beach", "Mission District"): 17,
}

# Define meeting constraints
meetings = {
    "Jessica": {
        "location": "Golden Gate Park",
        "available_from": "13:45",
        "available_to": "15:00",
        "duration": 30
    },
    "Ashley": {
        "location": "Bayview",
        "available_from": "17:15",
        "available_to": "20:00",
        "duration": 105
    },
    "Ronald": {
        "location": "Chinatown",
        "available_from": "07:15",
        "available_to": "14:45",
        "duration": 90
    },
    "William": {
        "location": "North Beach",
        "available_from": "13:15",
        "available_to": "20:15",
        "duration": 15
    },
    "Daniel": {
        "location": "Mission District",
        "available_from": "07:00",
        "available_to": "11:15",
        "duration": 105
    }
}

# Convert time strings to datetime objects for easier manipulation
def time_str_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

def datetime_to_time_str(time_dt):
    return time_dt.strftime('%H:%M')

# Function to find meeting schedule
def find_schedule():
    start_time = time_str_to_datetime("09:00")
    itinerary = []
    
    # Meeting with Ronald first (as he's available from morning)
    ronald_avail_from = time_str_to_datetime(meetings["Ronald"]["available_from"])
    ronald_avail_to = time_str_to_datetime(meetings["Ronald"]["available_to"])
    
    # Calculate travel time to Chinatown from Presidio
    travel_time_to_ronald = travel_times[("Presidio", "Chinatown")]
    time_to_meet_ronald = start_time + timedelta(minutes=travel_time_to_ronald)
    
    if time_to_meet_ronald <= ronald_avail_to - timedelta(minutes=meetings["Ronald"]["duration"]):
        meet_ronald_start = max(time_to_meet_ronald, ronald_avail_from)
        meet_ronald_end = meet_ronald_start + timedelta(minutes=meetings["Ronald"]["duration"])
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Ronald",
            "start_time": datetime_to_time_str(meet_ronald_start),
            "end_time": datetime_to_time_str(meet_ronald_end),
        })
        start_time = meet_ronald_end + timedelta(minutes=travel_time_to_ronald)  # travel back to Presidio

    # Meeting with Jessica next
    jessica_avail_from = time_str_to_datetime(meetings["Jessica"]["available_from"])
    jessica_avail_to = time_str_to_datetime(meetings["Jessica"]["available_to"])

    travel_time_to_jessica = travel_times[("Presidio", "Golden Gate Park")]
    time_to_meet_jessica = start_time + timedelta(minutes=travel_time_to_jessica)

    if time_to_meet_jessica <= jessica_avail_to - timedelta(minutes=meetings["Jessica"]["duration"]):
        meet_jessica_start = max(time_to_meet_jessica, jessica_avail_from)
        meet_jessica_end = meet_jessica_start + timedelta(minutes=meetings["Jessica"]["duration"])
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Jessica",
            "start_time": datetime_to_time_str(meet_jessica_start),
            "end_time": datetime_to_time_str(meet_jessica_end),
        })
        start_time = meet_jessica_end + timedelta(minutes=travel_time_to_jessica)  # travel back to Presidio

    # Meeting with William
    william_avail_from = time_str_to_datetime(meetings["William"]["available_from"])
    william_avail_to = time_str_to_datetime(meetings["William"]["available_to"])

    travel_time_to_william = travel_times[("Presidio", "North Beach")]
    time_to_meet_william = start_time + timedelta(minutes=travel_time_to_william)

    if time_to_meet_william <= william_avail_to - timedelta(minutes=meetings["William"]["duration"]):
        meet_william_start = max(time_to_meet_william, william_avail_from)
        meet_william_end = meet_william_start + timedelta(minutes=meetings["William"]["duration"])
        itinerary.append({
            "action": "meet",
            "location": "North Beach",
            "person": "William",
            "start_time": datetime_to_time_str(meet_william_start),
            "end_time": datetime_to_time_str(meet_william_end),
        })
        start_time = meet_william_end + timedelta(minutes=travel_time_to_william)  # travel back to Presidio

    # Meeting with Ashley last
    ashley_avail_from = time_str_to_datetime(meetings["Ashley"]["available_from"])
    ashley_avail_to = time_str_to_datetime(meetings["Ashley"]["available_to"])

    travel_time_to_ashley = travel_times[("Presidio", "Bayview")]
    time_to_meet_ashley = start_time + timedelta(minutes=travel_time_to_ashley)

    if time_to_meet_ashley <= ashley_avail_to - timedelta(minutes=meetings["Ashley"]["duration"]):
        meet_ashley_start = max(time_to_meet_ashley, ashley_avail_from)
        meet_ashley_end = meet_ashley_start + timedelta(minutes=meetings["Ashley"]["duration"])
        itinerary.append({
            "action": "meet",
            "location": "Bayview",
            "person": "Ashley",
            "start_time": datetime_to_time_str(meet_ashley_start),
            "end_time": datetime_to_time_str(meet_ashley_end),
        })

    # Meeting with Daniel
    daniel_avail_from = time_str_to_datetime(meetings["Daniel"]["available_from"])
    daniel_avail_to = time_str_to_datetime(meetings["Daniel"]["available_to"])

    time_to_meet_daniel = datetime.strptime("07:00", "%H:%M") + timedelta(minutes=travel_times[("Presidio", "Mission District")])
    
    if time_to_meet_daniel <= daniel_avail_to - timedelta(minutes=meetings["Daniel"]["duration"]):
        meet_daniel_start = max(time_to_meet_daniel, daniel_avail_from)
        meet_daniel_end = meet_daniel_start + timedelta(minutes=meetings["Daniel"]["duration"])
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Daniel",
            "start_time": datetime_to_time_str(meet_daniel_start),
            "end_time": datetime_to_time_str(meet_daniel_end),
        })

    return json.dumps({"itinerary": itinerary}, indent=2)

# Run the schedule computation
if __name__ == "__main__":
    schedule = find_schedule()
    print("SOLUTION:")
    print(schedule)