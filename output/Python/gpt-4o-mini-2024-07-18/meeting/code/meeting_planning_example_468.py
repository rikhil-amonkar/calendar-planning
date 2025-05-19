import json
from datetime import datetime, timedelta

def travel_time(from_location, to_location):
    times = {
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Golden Gate Park"): 11,
        ("Bayview", "The Castro"): 20,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Golden Gate Park"): 22,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Fisherman's Wharf", "The Castro"): 26,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
    }
    
    return times.get((from_location, to_location), 0)

def schedule_meetings():
    now = datetime.strptime("9:00", "%H:%M")
    schedule = []
    
    # Define the time windows for each person with the travel time included
    time_windows = {
        "Rebecca": {"location": "Bayview", "start": now, "end": now + timedelta(minutes=165)},  # 9:00 to 12:45
        "Amanda": {"location": "Pacific Heights", "start": datetime.strptime("18:30", "%H:%M"), 
                   "end": datetime.strptime("21:45", "%H:%M")},  # 6:30PM to 9:45PM
        "James": {"location": "Alamo Square", "start": datetime.strptime("9:45", "%H:%M"), 
                  "end": datetime.strptime("21:15", "%H:%M")},  # 9:45AM to 9:15PM
        "Sarah": {"location": "Fisherman's Wharf", "start": datetime.strptime("8:00", "%H:%M"), 
                  "end": datetime.strptime("21:30", "%H:%M")},  # 8:00AM to 9:30PM
        "Melissa": {"location": "Golden Gate Park", "start": now, 
                    "end": datetime.strptime("18:45", "%H:%M")},  # 9:00AM to 6:45PM
    }
    
    meetings = {
        "Rebecca": {"duration": 90},
        "Amanda": {"duration": 90},
        "James": {"duration": 90},
        "Sarah": {"duration": 90},
        "Melissa": {"duration": 90},
    }
    
    def can_meet(person, start, end):
        travel = travel_time("The Castro", time_windows[person]["location"])
        meeting_start = start + timedelta(minutes=travel)
        meeting_end = meeting_start + timedelta(minutes=meetings[person]["duration"])
        return (meeting_start >= time_windows[person]["start"] and 
                meeting_end <= time_windows[person]["end"])
    
    # Scheduling meetings
    current_time = now
    current_location = "The Castro"
    
    # Meeting Rebecca
    if can_meet("Rebecca", current_time, current_time):
        travel = travel_time(current_location, "Bayview")
        start_time = current_time + timedelta(minutes=travel)
        current_time = start_time + timedelta(minutes=meetings["Rebecca"]["duration"])
        schedule.append({
            "action": "meet",
            "location": "Bayview",
            "person": "Rebecca",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": current_time.strftime("%H:%M")
        })
        current_location = "Bayview"
    
    # Meeting James
    if can_meet("James", current_time, current_time):
        travel = travel_time(current_location, "Alamo Square")
        start_time = current_time + timedelta(minutes=travel)
        current_time = start_time + timedelta(minutes=meetings["James"]["duration"])
        schedule.append({
            "action": "meet",
            "location": "Alamo Square",
            "person": "James",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": current_time.strftime("%H:%M")
        })
        current_location = "Alamo Square"

    # Meeting Melissa
    if can_meet("Melissa", current_time, current_time):
        travel = travel_time(current_location, "Golden Gate Park")
        start_time = current_time + timedelta(minutes=travel)
        current_time = start_time + timedelta(minutes=meetings["Melissa"]["duration"])
        schedule.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Melissa",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": current_time.strftime("%H:%M")
        })
        current_location = "Golden Gate Park"

    # Meeting Amanda
    if can_meet("Amanda", current_time, current_time):
        travel = travel_time(current_location, "Pacific Heights")
        start_time = current_time + timedelta(minutes=travel)
        current_time = start_time + timedelta(minutes=meetings["Amanda"]["duration"])
        schedule.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Amanda",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": current_time.strftime("%H:%M")
        })
        current_location = "Pacific Heights"

    # Meeting Sarah
    if can_meet("Sarah", current_time, current_time):
        travel = travel_time(current_location, "Fisherman's Wharf")
        start_time = current_time + timedelta(minutes=travel)
        current_time = start_time + timedelta(minutes=meetings["Sarah"]["duration"])
        schedule.append({
            "action": "meet",
            "location": "Fisherman's Wharf",
            "person": "Sarah",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": current_time.strftime("%H:%M")
        })
    
    return json.dumps({"itinerary": schedule}, indent=2)

if __name__ == "__main__":
    print("SOLUTION:")
    print(schedule_meetings())