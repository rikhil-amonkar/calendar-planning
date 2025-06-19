import json
import datetime

# Input parameters
travel_distances = {
    "Union Square": {
        "Mission District": 14,
        "Bayview": 15,
        "Sunset District": 26
    },
    "Mission District": {
        "Union Square": 15,
        "Bayview": 15,
        "Sunset District": 24
    },
    "Bayview": {
        "Union Square": 17,
        "Mission District": 13,
        "Sunset District": 23
    },
    "Sunset District": {
        "Union Square": 30,
        "Mission District": 24,
        "Bayview": 22
    }
}

constraints = {
    "Rebecca": {"start_time": "11:30", "end_time": "20:15", "min_meeting_time": 120},
    "Karen": {"start_time": "12:45", "end_time": "15:00", "min_meeting_time": 120},
    "Carol": {"start_time": "10:15", "end_time": "11:45", "min_meeting_time": 30}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(schedule, person, location, start_time, end_time):
    meeting_start_time = datetime.datetime.strptime(start_time, "%H:%M")
    meeting_end_time = datetime.datetime.strptime(end_time, "%H:%M")
    
    person_start_time = datetime.datetime.strptime(constraints[person]["start_time"], "%H:%M")
    person_end_time = datetime.datetime.strptime(constraints[person]["end_time"], "%H:%M")
    
    if meeting_start_time < person_start_time:
        return False
    if meeting_end_time > person_end_time:
        return False
    
    return True

def compute_schedule():
    schedule = []
    current_time = datetime.datetime.strptime("09:00", "%H:%M")
    
    # Travel to Sunset District
    schedule.append({
        "action": "travel",
        "location": "Sunset District",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + datetime.timedelta(minutes=calculate_travel_time("Union Square", "Sunset District"))).strftime("%H:%M")
    })
    current_time = datetime.datetime.strptime((current_time + datetime.timedelta(minutes=calculate_travel_time("Union Square", "Sunset District"))).strftime("%H:%M"), "%H:%M")
    
    # Meet Carol at Sunset District
    schedule.append({
        "action": "meet",
        "location": "Sunset District",
        "person": "Carol",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + datetime.timedelta(minutes=constraints["Carol"]["min_meeting_time"])).strftime("%H:%M")
    })
    current_time = datetime.datetime.strptime((current_time + datetime.timedelta(minutes=constraints["Carol"]["min_meeting_time"])).strftime("%H:%M"), "%H:%M")
    
    # Travel to Mission District
    schedule.append({
        "action": "travel",
        "location": "Mission District",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + datetime.timedelta(minutes=calculate_travel_time("Sunset District", "Mission District"))).strftime("%H:%M")
    })
    current_time = datetime.datetime.strptime((current_time + datetime.timedelta(minutes=calculate_travel_time("Sunset District", "Mission District"))).strftime("%H:%M"), "%H:%M")
    
    # Meet Rebecca at Mission District
    schedule.append({
        "action": "meet",
        "location": "Mission District",
        "person": "Rebecca",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + datetime.timedelta(minutes=constraints["Rebecca"]["min_meeting_time"])).strftime("%H:%M")
    })
    current_time = datetime.datetime.strptime((current_time + datetime.timedelta(minutes=constraints["Rebecca"]["min_meeting_time"])).strftime("%H:%M"), "%H:%M")
    
    # Travel to Bayview
    schedule.append({
        "action": "travel",
        "location": "Bayview",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + datetime.timedelta(minutes=calculate_travel_time("Mission District", "Bayview"))).strftime("%H:%M")
    })
    current_time = datetime.datetime.strptime((current_time + datetime.timedelta(minutes=calculate_travel_time("Mission District", "Bayview"))).strftime("%H:%M"), "%H:%M")
    
    # Meet Karen at Bayview
    schedule.append({
        "action": "meet",
        "location": "Bayview",
        "person": "Karen",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + datetime.timedelta(minutes=constraints["Karen"]["min_meeting_time"])).strftime("%H:%M")
    })
    current_time = datetime.datetime.strptime((current_time + datetime.timedelta(minutes=constraints["Karen"]["min_meeting_time"])).strftime("%H:%M"), "%H:%M")
    
    return schedule

def main():
    schedule = compute_schedule()
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()