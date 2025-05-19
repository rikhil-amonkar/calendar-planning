import json
from datetime import datetime, timedelta
import itertools

# Define travel distances in minutes
travel_distances = {
    "Chinatown": {
        "Mission District": 18,
        "Alamo Square": 17,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Golden Gate Park": 23,
        "Sunset District": 29,
        "Presidio": 19
    },
    "Mission District": {
        "Chinatown": 16,
        "Alamo Square": 11,
        "Pacific Heights": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Sunset District": 24,
        "Presidio": 25
    },
    "Alamo Square": {
        "Chinatown": 16,
        "Mission District": 10,
        "Pacific Heights": 10,
        "Union Square": 14,
        "Golden Gate Park": 9,
        "Sunset District": 16,
        "Presidio": 18
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Mission District": 15,
        "Alamo Square": 10,
        "Union Square": 12,
        "Golden Gate Park": 15,
        "Sunset District": 21,
        "Presidio": 11
    },
    "Union Square": {
        "Chinatown": 7,
        "Mission District": 14,
        "Alamo Square": 15,
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "Sunset District": 26,
        "Presidio": 24
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Mission District": 17,
        "Alamo Square": 10,
        "Pacific Heights": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Presidio": 11
    },
    "Sunset District": {
        "Chinatown": 30,
        "Mission District": 24,
        "Alamo Square": 17,
        "Pacific Heights": 21,
        "Union Square": 30,
        "Golden Gate Park": 11,
        "Presidio": 16
    },
    "Presidio": {
        "Chinatown": 21,
        "Mission District": 26,
        "Alamo Square": 18,
        "Pacific Heights": 11,
        "Union Square": 22,
        "Golden Gate Park": 12,
        "Sunset District": 15
    }
}

# Define meeting constraints
constraints = {
    "David": {"location": "Mission District", "start_time": "08:00", "end_time": "19:45", "duration": 45},
    "Kenneth": {"location": "Alamo Square", "start_time": "14:00", "end_time": "19:45", "duration": 120},
    "John": {"location": "Pacific Heights", "start_time": "17:00", "end_time": "20:00", "duration": 15},
    "Charles": {"location": "Union Square", "start_time": "21:45", "end_time": "22:45", "duration": 60},
    "Deborah": {"location": "Golden Gate Park", "start_time": "07:00", "end_time": "18:15", "duration": 90},
    "Karen": {"location": "Sunset District", "start_time": "17:45", "end_time": "21:15", "duration": 15},
    "Carol": {"location": "Presidio", "start_time": "08:15", "end_time": "09:15", "duration": 30}
}

def calculate_travel_time(start_location, end_location):
    if start_location == "Chinatown":
        return travel_distances["Chinatown"][end_location]
    elif start_location == "Mission District":
        return travel_distances["Mission District"][end_location]
    elif start_location == "Alamo Square":
        return travel_distances["Alamo Square"][end_location]
    elif start_location == "Pacific Heights":
        return travel_distances["Pacific Heights"][end_location]
    elif start_location == "Union Square":
        return travel_distances["Union Square"][end_location]
    elif start_location == "Golden Gate Park":
        return travel_distances["Golden Gate Park"][end_location]
    elif start_location == "Sunset District":
        return travel_distances["Sunset District"][end_location]
    elif start_location == "Presidio":
        return travel_distances["Presidio"][end_location]

def check_constraint(person, start_time, end_time):
    constraint = constraints[person]
    if start_time >= constraint["start_time"] and end_time <= constraint["end_time"]:
        return True
    return False

def schedule_meeting(person, start_time, end_time):
    if check_constraint(person, start_time, end_time):
        return {"action": "meet", "location": constraints[person]["location"], "person": person, "start_time": start_time, "end_time": end_time}
    return None

def generate_itinerary():
    start_time = "09:00"
    end_time = "22:00"
    start_location = "Chinatown"
    itinerary = []
    
    # Generate all possible meeting times
    for hour in range(9, 22):
        for minute in range(0, 60):
            meeting_time = f"{hour:02d}:{minute:02d}"
            if meeting_time >= constraints["David"]["start_time"] and meeting_time <= constraints["David"]["end_time"]:
                itinerary.append(schedule_meeting("David", meeting_time, meeting_time))
            if meeting_time >= constraints["Kenneth"]["start_time"] and meeting_time <= constraints["Kenneth"]["end_time"]:
                itinerary.append(schedule_meeting("Kenneth", meeting_time, meeting_time))
            if meeting_time >= constraints["John"]["start_time"] and meeting_time <= constraints["John"]["end_time"]:
                itinerary.append(schedule_meeting("John", meeting_time, meeting_time))
            if meeting_time >= constraints["Charles"]["start_time"] and meeting_time <= constraints["Charles"]["end_time"]:
                itinerary.append(schedule_meeting("Charles", meeting_time, meeting_time))
            if meeting_time >= constraints["Deborah"]["start_time"] and meeting_time <= constraints["Deborah"]["end_time"]:
                itinerary.append(schedule_meeting("Deborah", meeting_time, meeting_time))
            if meeting_time >= constraints["Karen"]["start_time"] and meeting_time <= constraints["Karen"]["end_time"]:
                itinerary.append(schedule_meeting("Karen", meeting_time, meeting_time))
            if meeting_time >= constraints["Carol"]["start_time"] and meeting_time <= constraints["Carol"]["end_time"]:
                itinerary.append(schedule_meeting("Carol", meeting_time, meeting_time))
    
    # Remove duplicates and sort by start time
    itinerary = list(set(itinerary))
    itinerary.sort(key=lambda x: x["start_time"])
    
    return itinerary

def optimize_itinerary(itinerary):
    optimized_itinerary = []
    current_location = "Chinatown"
    for meeting in itinerary:
        travel_time = calculate_travel_time(current_location, meeting["location"])
        start_time = datetime.strptime(meeting["start_time"], "%H:%M") + timedelta(minutes=travel_time)
        end_time = datetime.strptime(meeting["end_time"], "%H:%M") + timedelta(minutes=travel_time)
        optimized_itinerary.append({"action": "meet", "location": meeting["location"], "person": meeting["person"], "start_time": start_time.strftime("%H:%M"), "end_time": end_time.strftime("%H:%M")})
        current_location = meeting["location"]
    return optimized_itinerary

def main():
    itinerary = generate_itinerary()
    optimized_itinerary = optimize_itinerary(itinerary)
    result = {"itinerary": optimized_itinerary}
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()