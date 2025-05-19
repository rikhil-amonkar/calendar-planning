import json
from datetime import datetime, timedelta
import itertools

# Define travel distances in minutes
travel_distances = {
    "Golden Gate Park": {
        "Alamo Square": 10,
        "Presidio": 11,
        "Russian Hill": 19
    },
    "Alamo Square": {
        "Golden Gate Park": 9,
        "Presidio": 18,
        "Russian Hill": 13
    },
    "Presidio": {
        "Golden Gate Park": 12,
        "Alamo Square": 18,
        "Russian Hill": 14
    },
    "Russian Hill": {
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Presidio": 14
    }
}

# Define meeting constraints
constraints = {
    "Timothy": {"location": "Alamo Square", "start_time": "12:00", "end_time": "16:15", "duration": 105},
    "Mark": {"location": "Presidio", "start_time": "18:45", "end_time": "21:00", "duration": 60},
    "Joseph": {"location": "Russian Hill", "start_time": "16:45", "end_time": "21:30", "duration": 60}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

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
    end_time = "21:00"
    start_location = "Golden Gate Park"
    itinerary = []
    
    # Generate all possible meeting times
    for hour in range(9, 21):
        for minute in range(0, 60):
            meeting_time = f"{hour:02d}:{minute:02d}"
            if meeting_time >= constraints["Timothy"]["start_time"] and meeting_time <= constraints["Timothy"]["end_time"]:
                itinerary.append(schedule_meeting("Timothy", meeting_time, meeting_time))
            if meeting_time >= constraints["Mark"]["start_time"] and meeting_time <= constraints["Mark"]["end_time"]:
                itinerary.append(schedule_meeting("Mark", meeting_time, meeting_time))
            if meeting_time >= constraints["Joseph"]["start_time"] and meeting_time <= constraints["Joseph"]["end_time"]:
                itinerary.append(schedule_meeting("Joseph", meeting_time, meeting_time))
    
    # Remove duplicates and sort by start time
    itinerary = list(set(itinerary))
    itinerary.sort(key=lambda x: x["start_time"])
    
    return itinerary

def optimize_itinerary(itinerary):
    optimized_itinerary = []
    current_location = "Golden Gate Park"
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