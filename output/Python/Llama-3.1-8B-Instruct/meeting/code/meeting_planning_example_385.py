import json
from datetime import datetime, timedelta
import itertools

# Define travel distances in minutes
travel_distances = {
    "Nob Hill": {
        "Presidio": 17,
        "North Beach": 8,
        "Fisherman's Wharf": 11,
        "Pacific Heights": 8
    },
    "Presidio": {
        "Nob Hill": 18,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Pacific Heights": 11
    },
    "North Beach": {
        "Nob Hill": 7,
        "Presidio": 17,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    },
    "Fisherman's Wharf": {
        "Nob Hill": 11,
        "Presidio": 17,
        "North Beach": 6,
        "Pacific Heights": 12
    },
    "Pacific Heights": {
        "Nob Hill": 8,
        "Presidio": 11,
        "North Beach": 9,
        "Fisherman's Wharf": 13
    }
}

# Define meeting constraints
constraints = {
    "Jeffrey": {"location": "Presidio", "start_time": "08:00", "end_time": "10:00", "duration": 105},
    "Steven": {"location": "North Beach", "start_time": "13:30", "end_time": "22:00", "duration": 45},
    "Barbara": {"location": "Fisherman's Wharf", "start_time": "18:00", "end_time": "21:30", "duration": 30},
    "John": {"location": "Pacific Heights", "start_time": "09:00", "end_time": "13:30", "duration": 15}
}

def calculate_travel_time(start_location, end_location):
    if start_location == "Nob Hill":
        return travel_distances["Nob Hill"][end_location]
    elif start_location == "Presidio":
        return travel_distances["Presidio"][end_location]
    elif start_location == "North Beach":
        return travel_distances["North Beach"][end_location]
    elif start_location == "Fisherman's Wharf":
        return travel_distances["Fisherman's Wharf"][end_location]
    elif start_location == "Pacific Heights":
        return travel_distances["Pacific Heights"][end_location]

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
    start_location = "Nob Hill"
    itinerary = []
    
    # Generate all possible meeting times
    for hour in range(9, 22):
        for minute in range(0, 60):
            meeting_time = f"{hour:02d}:{minute:02d}"
            if meeting_time >= constraints["Jeffrey"]["start_time"] and meeting_time <= constraints["Jeffrey"]["end_time"]:
                itinerary.append(schedule_meeting("Jeffrey", meeting_time, meeting_time))
            if meeting_time >= constraints["Steven"]["start_time"] and meeting_time <= constraints["Steven"]["end_time"]:
                itinerary.append(schedule_meeting("Steven", meeting_time, meeting_time))
            if meeting_time >= constraints["Barbara"]["start_time"] and meeting_time <= constraints["Barbara"]["end_time"]:
                itinerary.append(schedule_meeting("Barbara", meeting_time, meeting_time))
            if meeting_time >= constraints["John"]["start_time"] and meeting_time <= constraints["John"]["end_time"]:
                itinerary.append(schedule_meeting("John", meeting_time, meeting_time))
    
    # Remove duplicates and sort by start time
    itinerary = list(set(itinerary))
    itinerary.sort(key=lambda x: x["start_time"])
    
    return itinerary

def optimize_itinerary(itinerary):
    optimized_itinerary = []
    current_location = "Nob Hill"
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