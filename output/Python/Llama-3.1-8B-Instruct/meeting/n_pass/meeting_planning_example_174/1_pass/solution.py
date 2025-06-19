import json
from datetime import datetime, timedelta

def compute_travel_time(origin, destination, travel_times):
    return travel_times[f"{origin}-{destination}"]

def compute_meeting_schedule(arrival_time, thomas_constraints, kenneth_constraints, travel_times):
    schedule = []
    current_time = datetime.strptime(arrival_time, "%H:%M")
    
    # Meet Thomas
    thomas_meeting_time = max(thomas_constraints['start_time'], current_time + timedelta(minutes=compute_travel_time('Nob Hill', 'Pacific Heights', travel_times)))
    thomas_meeting_end_time = thomas_meeting_time + timedelta(minutes=75)
    
    if thomas_meeting_time < thomas_constraints['end_time'] and thomas_meeting_end_time <= thomas_constraints['end_time']:
        schedule.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Thomas",
            "start_time": thomas_meeting_time.strftime("%H:%M"),
            "end_time": thomas_meeting_end_time.strftime("%H:%M")
        })
        current_time = thomas_meeting_end_time
    
    # Meet Kenneth
    kenneth_meeting_time = max(kenneth_constraints['start_time'], current_time + timedelta(minutes=compute_travel_time('Nob Hill', 'Mission District', travel_times)))
    kenneth_meeting_end_time = kenneth_meeting_time + timedelta(minutes=45)
    
    if kenneth_meeting_time < kenneth_constraints['end_time'] and kenneth_meeting_end_time <= kenneth_constraints['end_time']:
        schedule.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Kenneth",
            "start_time": kenneth_meeting_time.strftime("%H:%M"),
            "end_time": kenneth_meeting_end_time.strftime("%H:%M")
        })
        current_time = kenneth_meeting_end_time
    
    return schedule

def main():
    travel_times = {
        "Nob Hill-Pacific Heights": 8,
        "Nob Hill-Mission District": 13,
        "Pacific Heights-Nob Hill": 8,
        "Pacific Heights-Mission District": 15,
        "Mission District-Nob Hill": 12,
        "Mission District-Pacific Heights": 16
    }
    
    arrival_time = "09:00"
    thomas_constraints = {
        "start_time": "15:30",
        "end_time": "19:15"
    }
    kenneth_constraints = {
        "start_time": "12:00",
        "end_time": "15:45"
    }
    
    schedule = compute_meeting_schedule(arrival_time, thomas_constraints, kenneth_constraints, travel_times)
    
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()