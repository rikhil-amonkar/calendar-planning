import json
from datetime import datetime, timedelta
import itertools

# Define travel distances in minutes
travel_distances = {
    "Bayview": {
        "Nob Hill": 20,
        "Union Square": 17,
        "Chinatown": 18,
        "The Castro": 20,
        "Presidio": 31,
        "Pacific Heights": 23,
        "Russian Hill": 23
    },
    "Nob Hill": {
        "Bayview": 19,
        "Union Square": 7,
        "Chinatown": 6,
        "The Castro": 17,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Russian Hill": 5
    },
    "Union Square": {
        "Bayview": 15,
        "Nob Hill": 9,
        "Chinatown": 7,
        "The Castro": 19,
        "Presidio": 24,
        "Pacific Heights": 15,
        "Russian Hill": 13
    },
    "Chinatown": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 7,
        "The Castro": 22,
        "Presidio": 19,
        "Pacific Heights": 10,
        "Russian Hill": 7
    },
    "The Castro": {
        "Bayview": 19,
        "Nob Hill": 16,
        "Union Square": 19,
        "Chinatown": 20,
        "Presidio": 20,
        "Pacific Heights": 16,
        "Russian Hill": 18
    },
    "Presidio": {
        "Bayview": 31,
        "Nob Hill": 18,
        "Union Square": 22,
        "Chinatown": 21,
        "The Castro": 21,
        "Pacific Heights": 11,
        "Russian Hill": 14
    },
    "Pacific Heights": {
        "Bayview": 22,
        "Nob Hill": 8,
        "Union Square": 12,
        "Chinatown": 11,
        "The Castro": 16,
        "Presidio": 11,
        "Russian Hill": 7
    },
    "Russian Hill": {
        "Bayview": 23,
        "Nob Hill": 5,
        "Union Square": 11,
        "Chinatown": 9,
        "The Castro": 21,
        "Presidio": 14,
        "Pacific Heights": 7
    }
}

# Define meeting constraints
constraints = {
    "Paul": {"location": "Nob Hill", "start_time": "16:15", "end_time": "21:15", "duration": 60},
    "Carol": {"location": "Union Square", "start_time": "18:00", "end_time": "20:15", "duration": 120},
    "Patricia": {"location": "Chinatown", "start_time": "20:00", "end_time": "21:30", "duration": 75},
    "Karen": {"location": "The Castro", "start_time": "17:00", "end_time": "19:00", "duration": 45},
    "Nancy": {"location": "Presidio", "start_time": "11:45", "end_time": "22:00", "duration": 30},
    "Jeffrey": {"location": "Pacific Heights", "start_time": "20:00", "end_time": "20:45", "duration": 45},
    "Matthew": {"location": "Russian Hill", "start_time": "15:45", "end_time": "21:45", "duration": 75}
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
    start_location = "Bayview"
    itinerary = []
    
    # Generate all possible meeting times
    for hour in range(9, 21):
        for minute in range(0, 60):
            meeting_time = f"{hour:02d}:{minute:02d}"
            if meeting_time >= constraints["Paul"]["start_time"] and meeting_time <= constraints["Paul"]["end_time"]:
                itinerary.append(schedule_meeting("Paul", meeting_time, meeting_time))
            if meeting_time >= constraints["Carol"]["start_time"] and meeting_time <= constraints["Carol"]["end_time"]:
                itinerary.append(schedule_meeting("Carol", meeting_time, meeting_time))
            if meeting_time >= constraints["Patricia"]["start_time"] and meeting_time <= constraints["Patricia"]["end_time"]:
                itinerary.append(schedule_meeting("Patricia", meeting_time, meeting_time))
            if meeting_time >= constraints["Karen"]["start_time"] and meeting_time <= constraints["Karen"]["end_time"]:
                itinerary.append(schedule_meeting("Karen", meeting_time, meeting_time))
            if meeting_time >= constraints["Nancy"]["start_time"] and meeting_time <= constraints["Nancy"]["end_time"]:
                itinerary.append(schedule_meeting("Nancy", meeting_time, meeting_time))
            if meeting_time >= constraints["Jeffrey"]["start_time"] and meeting_time <= constraints["Jeffrey"]["end_time"]:
                itinerary.append(schedule_meeting("Jeffrey", meeting_time, meeting_time))
            if meeting_time >= constraints["Matthew"]["start_time"] and meeting_time <= constraints["Matthew"]["end_time"]:
                itinerary.append(schedule_meeting("Matthew", meeting_time, meeting_time))
    
    # Remove duplicates and sort by start time
    itinerary = list(set(itinerary))
    itinerary.sort(key=lambda x: x["start_time"])
    
    return itinerary

def optimize_itinerary(itinerary):
    optimized_itinerary = []
    current_location = "Bayview"
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