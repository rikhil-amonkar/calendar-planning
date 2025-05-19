import json
from datetime import datetime, timedelta
import itertools

# Define travel distances in minutes
travel_distances = {
    "Pacific Heights": {
        "North Beach": 9,
        "Financial District": 13,
        "Alamo Square": 10,
        "Mission District": 15
    },
    "North Beach": {
        "Pacific Heights": 8,
        "Financial District": 8,
        "Alamo Square": 16,
        "Mission District": 18
    },
    "Financial District": {
        "Pacific Heights": 13,
        "North Beach": 7,
        "Alamo Square": 17,
        "Mission District": 17
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "North Beach": 15,
        "Financial District": 17,
        "Mission District": 10
    },
    "Mission District": {
        "Pacific Heights": 16,
        "North Beach": 17,
        "Financial District": 17,
        "Alamo Square": 11
    }
}

# Define meeting constraints
constraints = {
    "Helen": {"location": "North Beach", "start_time": "09:00", "end_time": "17:00", "duration": 15},
    "Betty": {"location": "Financial District", "start_time": "19:00", "end_time": "21:45", "duration": 90},
    "Amanda": {"location": "Alamo Square", "start_time": "19:45", "end_time": "21:00", "duration": 60},
    "Kevin": {"location": "Mission District", "start_time": "10:45", "end_time": "14:45", "duration": 45}
}

def calculate_travel_time(start_location, end_location):
    if start_location == "Pacific Heights":
        return travel_distances["Pacific Heights"][end_location]
    elif start_location == "North Beach":
        return travel_distances["North Beach"][end_location]
    elif start_location == "Financial District":
        return travel_distances["Financial District"][end_location]
    elif start_location == "Alamo Square":
        return travel_distances["Alamo Square"][end_location]
    elif start_location == "Mission District":
        return travel_distances["Mission District"][end_location]

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
    start_location = "Pacific Heights"
    itinerary = []
    
    # Generate all possible meeting times
    for hour in range(9, 22):
        for minute in range(0, 60):
            meeting_time = f"{hour:02d}:{minute:02d}"
            if meeting_time >= constraints["Helen"]["start_time"] and meeting_time <= constraints["Helen"]["end_time"]:
                itinerary.append(schedule_meeting("Helen", meeting_time, meeting_time))
            if meeting_time >= constraints["Betty"]["start_time"] and meeting_time <= constraints["Betty"]["end_time"]:
                itinerary.append(schedule_meeting("Betty", meeting_time, meeting_time))
            if meeting_time >= constraints["Amanda"]["start_time"] and meeting_time <= constraints["Amanda"]["end_time"]:
                itinerary.append(schedule_meeting("Amanda", meeting_time, meeting_time))
            if meeting_time >= constraints["Kevin"]["start_time"] and meeting_time <= constraints["Kevin"]["end_time"]:
                itinerary.append(schedule_meeting("Kevin", meeting_time, meeting_time))
    
    # Remove duplicates and sort by start time
    itinerary = list(set(itinerary))
    itinerary.sort(key=lambda x: x["start_time"])
    
    return itinerary

def optimize_itinerary(itinerary):
    optimized_itinerary = []
    current_location = "Pacific Heights"
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