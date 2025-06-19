import json
import datetime
from typing import List, Dict

def calculate_travel_time(origin: str, destination: str, travel_times: Dict[str, Dict[str, int]]) -> int:
    return travel_times[origin][destination]

def is_available(location: str, start_time: str, end_time: str, availability: Dict[str, List[str]]) -> bool:
    # Parse the end time to remove the string " + X minutes"
    end_time = end_time.split(' + ')[0]
    
    start_hour, start_minute = map(int, start_time.split(':'))
    end_hour, end_minute = map(int, end_time.split(':'))
    
    for time in availability[location]:
        hour, minute = map(int, time.split(':'))
        if start_hour < hour < end_hour or (start_hour == hour and start_minute <= minute):
            return False
    return True

def compute_meeting_schedule(
    union_square_start: str,
    betty_start: str,
    betty_end: str,
    melissa_start: str,
    melissa_end: str,
    joshua_start: str,
    joshua_end: str,
    jeffrey_start: str,
    jeffrey_end: str,
    james_start: str,
    james_end: str,
    anthony_start: str,
    anthony_end: str,
    timothy_start: str,
    timothy_end: str,
    emily_start: str,
    emily_end: str,
    travel_times: Dict[str, Dict[str, int]],
    availability: Dict[str, List[str]]
) -> List[Dict]:
    union_square = "Union Square"
    locations = ["Russian Hill", "Alamo Square", "Haight-Ashbury", "Marina District", "Bayview", "Chinatown", "Presidio", "Sunset District"]
    people = ["Betty", "Melissa", "Joshua", "Jeffrey", "James", "Anthony", "Timothy", "Emily"]
    
    schedule = []
    current_time = union_square_start
    
    # Meet Betty
    if is_available("Russian Hill", current_time, betty_end.split(' + ')[0], availability):
        schedule.append({"action": "meet", "location": "Russian Hill", "person": "Betty", "start_time": current_time, "end_time": betty_end.split(' + ')[0]})
        current_time = betty_end.split(' + ')[0]
        travel_time = calculate_travel_time("Russian Hill", "Union Square", travel_times)
        schedule.append({"action": "travel", "location": "Union Square", "person": "Betty", "start_time": current_time, "end_time": (datetime.datetime.strptime(current_time, "%H:%M")).strftime("%H:%M") + " + " + str(travel_time) + " minutes"})
    
    # Meet Melissa
    if is_available("Alamo Square", current_time, melissa_end.split(' + ')[0], availability):
        schedule.append({"action": "meet", "location": "Alamo Square", "person": "Melissa", "start_time": current_time, "end_time": melissa_end.split(' + ')[0]})
        current_time = melissa_end.split(' + ')[0]
        travel_time = calculate_travel_time("Alamo Square", "Union Square", travel_times)
        schedule.append({"action": "travel", "location": "Union Square", "person": "Melissa", "start_time": current_time, "end_time": (datetime.datetime.strptime(current_time, "%H:%M")).strftime("%H:%M") + " + " + str(travel_time) + " minutes"})
    
    # Meet Joshua
    if is_available("Haight-Ashbury", current_time, joshua_end.split(' + ')[0], availability):
        schedule.append({"action": "meet", "location": "Haight-Ashbury", "person": "Joshua", "start_time": current_time, "end_time": joshua_end.split(' + ')[0]})
        current_time = joshua_end.split(' + ')[0]
        travel_time = calculate_travel_time("Haight-Ashbury", "Union Square", travel_times)
        schedule.append({"action": "travel", "location": "Union Square", "person": "Joshua", "start_time": current_time, "end_time": (datetime.datetime.strptime(current_time, "%H:%M")).strftime("%H:%M") + " + " + str(travel_time) + " minutes"})
    
    # Meet Jeffrey
    if is_available("Marina District", current_time, "18:00", availability):
        schedule.append({"action": "meet", "location": "Marina District", "person": "Jeffrey", "start_time": current_time, "end_time": "18:00"})
        current_time = "18:00"
        travel_time = calculate_travel_time("Marina District", "Union Square", travel_times)
        schedule.append({"action": "travel", "location": "Union Square", "person": "Jeffrey", "start_time": current_time, "end_time": (datetime.datetime.strptime(current_time, "%H:%M")).strftime("%H:%M") + " + " + str(travel_time) + " minutes"})
    
    # Meet James
    if is_available("Bayview", current_time, james_end.split(' + ')[0], availability):
        schedule.append({"action": "meet", "location": "Bayview", "person": "James", "start_time": current_time, "end_time": james_end.split(' + ')[0]})
        current_time = james_end.split(' + ')[0]
        travel_time = calculate_travel_time("Bayview", "Union Square", travel_times)
        schedule.append({"action": "travel", "location": "Union Square", "person": "James", "start_time": current_time, "end_time": (datetime.datetime.strptime(current_time, "%H:%M")).strftime("%H:%M") + " + " + str(travel_time) + " minutes"})
    
    # Meet Anthony
    if is_available("Chinatown", current_time, anthony_end.split(' + ')[0], availability):
        schedule.append({"action": "meet", "location": "Chinatown", "person": "Anthony", "start_time": current_time, "end_time": anthony_end.split(' + ')[0]})
        current_time = anthony_end.split(' + ')[0]
        travel_time = calculate_travel_time("Chinatown", "Union Square", travel_times)
        schedule.append({"action": "travel", "location": "Union Square", "person": "Anthony", "start_time": current_time, "end_time": (datetime.datetime.strptime(current_time, "%H:%M")).strftime("%H:%M") + " + " + str(travel_time) + " minutes"})
    
    # Meet Timothy
    if is_available("Presidio", current_time, timothy_end.split(' + ')[0], availability):
        schedule.append({"action": "meet", "location": "Presidio", "person": "Timothy", "start_time": current_time, "end_time": timothy_end.split(' + ')[0]})
        current_time = timothy_end.split(' + ')[0]
        travel_time = calculate_travel_time("Presidio", "Union Square", travel_times)
        schedule.append({"action": "travel", "location": "Union Square", "person": "Timothy", "start_time": current_time, "end_time": (datetime.datetime.strptime(current_time, "%H:%M")).strftime("%H:%M") + " + " + str(travel_time) + " minutes"})
    
    # Meet Emily
    if is_available("Sunset District", current_time, emily_end.split(' + ')[0], availability):
        schedule.append({"action": "meet", "location": "Sunset District", "person": "Emily", "start_time": current_time, "end_time": emily_end.split(' + ')[0]})
        current_time = emily_end.split(' + ')[0]
        travel_time = calculate_travel_time("Sunset District", "Union Square", travel_times)
        schedule.append({"action": "travel", "location": "Union Square", "person": "Emily", "start_time": current_time, "end_time": (datetime.datetime.strptime(current_time, "%H:%M")).strftime("%H:%M") + " + " + str(travel_time) + " minutes"})
    
    return schedule

def main():
    union_square_start = "09:00"
    betty_start = "07:00"
    betty_end = "16:45 + 10 minutes"
    melissa_start = "09:30"
    melissa_end = "17:15"
    joshua_start = "12:15"
    joshua_end = "19:00"
    jeffrey_start = "12:15"
    jeffrey_end = "18:00"
    james_start = "07:30"
    james_end = "20:00"
    anthony_start = "11:45"
    anthony_end = "13:30"
    timothy_start = "12:30"
    timothy_end = "14:45"
    emily_start = "19:30"
    emily_end = "21:30"

    travel_times = {
        "Union Square": {
            "Russian Hill": 13,
            "Alamo Square": 15,
            "Haight-Ashbury": 18,
            "Marina District": 18,
            "Bayview": 15,
            "Chinatown": 7,
            "Presidio": 24,
            "Sunset District": 27
        },
        "Russian Hill": {
            "Union Square": 10,
            "Alamo Square": 15,
            "Haight-Ashbury": 17,
            "Marina District": 7,
            "Bayview": 23,
            "Chinatown": 9,
            "Presidio": 14,
            "Sunset District": 23
        },
        "Alamo Square": {
            "Union Square": 14,
            "Russian Hill": 13,
            "Haight-Ashbury": 5,
            "Marina District": 15,
            "Bayview": 16,
            "Chinatown": 15,
            "Presidio": 17,
            "Sunset District": 16
        },
        "Haight-Ashbury": {
            "Union Square": 19,
            "Russian Hill": 17,
            "Alamo Square": 5,
            "Marina District": 17,
            "Bayview": 18,
            "Chinatown": 19,
            "Presidio": 15,
            "Sunset District": 15
        },
        "Marina District": {
            "Union Square": 16,
            "Russian Hill": 8,
            "Alamo Square": 15,
            "Haight-Ashbury": 16,
            "Bayview": 27,
            "Chinatown": 15,
            "Presidio": 10,
            "Sunset District": 19
        },
        "Bayview": {
            "Union Square": 18,
            "Russian Hill": 23,
            "Alamo Square": 16,
            "Haight-Ashbury": 19,
            "Marina District": 27,
            "Chinatown": 19,
            "Presidio": 32,
            "Sunset District": 23
        },
        "Chinatown": {
            "Union Square": 7,
            "Russian Hill": 7,
            "Alamo Square": 17,
            "Haight-Ashbury": 19,
            "Marina District": 12,
            "Bayview": 20,
            "Presidio": 19,
            "Sunset District": 29
        },
        "Presidio": {
            "Union Square": 22,
            "Russian Hill": 14,
            "Alamo Square": 19,
            "Haight-Ashbury": 15,
            "Marina District": 11,
            "Bayview": 31,
            "Chinatown": 21,
            "Sunset District": 15
        },
        "Sunset District": {
            "Union Square": 30,
            "Russian Hill": 24,
            "Alamo Square": 17,
            "Haight-Ashbury": 15,
            "Marina District": 21,
            "Bayview": 22,
            "Chinatown": 30,
            "Presidio": 16
        }
    }
    
    availability = {
        "Russian Hill": ["07:00", "16:45"],
        "Alamo Square": ["09:30", "17:15"],
        "Haight-Ashbury": ["12:15", "19:00"],
        "Marina District": ["12:15", "18:00"],
        "Bayview": ["07:30", "20:00"],
        "Chinatown": ["11:45", "13:30"],
        "Presidio": ["12:30", "14:45"],
        "Sunset District": ["19:30", "21:30"]
    }
    
    schedule = compute_meeting_schedule(
        union_square_start,
        betty_start,
        betty_end,
        melissa_start,
        melissa_end,
        joshua_start,
        joshua_end,
        jeffrey_start,
        jeffrey_end,
        james_start,
        james_end,
        anthony_start,
        anthony_end,
        timothy_start,
        timothy_end,
        emily_start,
        emily_end,
        travel_times,
        availability
    )
    
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()