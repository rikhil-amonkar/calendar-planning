import json
from datetime import datetime, timedelta
import itertools

# Define travel distances in minutes
travel_distances = {
    "Mission District": {
        "Alamo Square": 11,
        "Presidio": 25,
        "Russian Hill": 15,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Financial District": 15,
        "Marina District": 19
    },
    "Alamo Square": {
        "Mission District": 10,
        "Presidio": 17,
        "Russian Hill": 13,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Embarcadero": 16,
        "Financial District": 17,
        "Marina District": 15
    },
    "Presidio": {
        "Mission District": 26,
        "Alamo Square": 19,
        "Russian Hill": 14,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11
    },
    "Russian Hill": {
        "Mission District": 16,
        "Alamo Square": 15,
        "Presidio": 14,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7
    },
    "North Beach": {
        "Mission District": 18,
        "Alamo Square": 16,
        "Presidio": 17,
        "Russian Hill": 4,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "Alamo Square": 9,
        "Presidio": 11,
        "Russian Hill": 19,
        "North Beach": 23,
        "Richmond District": 7,
        "Embarcadero": 25,
        "Financial District": 26,
        "Marina District": 16
    },
    "Richmond District": {
        "Mission District": 20,
        "Alamo Square": 13,
        "Presidio": 7,
        "Russian Hill": 13,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "Marina District": 9
    },
    "Embarcadero": {
        "Mission District": 20,
        "Alamo Square": 19,
        "Presidio": 20,
        "Russian Hill": 8,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Financial District": 5,
        "Marina District": 12
    },
    "Financial District": {
        "Mission District": 17,
        "Alamo Square": 17,
        "Presidio": 22,
        "Russian Hill": 11,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Embarcadero": 4,
        "Marina District": 15
    },
    "Marina District": {
        "Mission District": 20,
        "Alamo Square": 15,
        "Presidio": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Financial District": 17
    }
}

# Define meeting constraints
constraints = {
    "Laura": {"location": "Alamo Square", "start_time": "14:30", "end_time": "16:15", "duration": 75},
    "Brian": {"location": "Presidio", "start_time": "10:15", "end_time": "17:00", "duration": 30},
    "Karen": {"location": "Russian Hill", "start_time": "18:00", "end_time": "20:15", "duration": 90},
    "Stephanie": {"location": "North Beach", "start_time": "10:15", "end_time": "16:00", "duration": 75},
    "Helen": {"location": "Golden Gate Park", "start_time": "11:30", "end_time": "21:45", "duration": 120},
    "Sandra": {"location": "Richmond District", "start_time": "08:00", "end_time": "15:15", "duration": 30},
    "Mary": {"location": "Embarcadero", "start_time": "16:45", "end_time": "18:45", "duration": 120},
    "Deborah": {"location": "Financial District", "start_time": "19:00", "end_time": "20:45", "duration": 105},
    "Elizabeth": {"location": "Marina District", "start_time": "08:30", "end_time": "13:15", "duration": 105}
}

def calculate_travel_time(start_location, end_location):
    if start_location == "Mission District":
        return travel_distances["Mission District"][end_location]
    elif start_location == "Alamo Square":
        return travel_distances["Alamo Square"][end_location]
    elif start_location == "Presidio":
        return travel_distances["Presidio"][end_location]
    elif start_location == "Russian Hill":
        return travel_distances["Russian Hill"][end_location]
    elif start_location == "North Beach":
        return travel_distances["North Beach"][end_location]
    elif start_location == "Golden Gate Park":
        return travel_distances["Golden Gate Park"][end_location]
    elif start_location == "Richmond District":
        return travel_distances["Richmond District"][end_location]
    elif start_location == "Embarcadero":
        return travel_distances["Embarcadero"][end_location]
    elif start_location == "Financial District":
        return travel_distances["Financial District"][end_location]
    elif start_location == "Marina District":
        return travel_distances["Marina District"][end_location]

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
    start_location = "Mission District"
    itinerary = []
    
    # Generate all possible meeting times
    for hour in range(9, 21):
        for minute in range(0, 60):
            meeting_time = f"{hour:02d}:{minute:02d}"
            if meeting_time >= constraints["Laura"]["start_time"] and meeting_time <= constraints["Laura"]["end_time"]:
                itinerary.append(schedule_meeting("Laura", meeting_time, meeting_time))
            if meeting_time >= constraints["Brian"]["start_time"] and meeting_time <= constraints["Brian"]["end_time"]:
                itinerary.append(schedule_meeting("Brian", meeting_time, meeting_time))
            if meeting_time >= constraints["Karen"]["start_time"] and meeting_time <= constraints["Karen"]["end_time"]:
                itinerary.append(schedule_meeting("Karen", meeting_time, meeting_time))
            if meeting_time >= constraints["Stephanie"]["start_time"] and meeting_time <= constraints["Stephanie"]["end_time"]:
                itinerary.append(schedule_meeting("Stephanie", meeting_time, meeting_time))
            if meeting_time >= constraints["Helen"]["start_time"] and meeting_time <= constraints["Helen"]["end_time"]:
                itinerary.append(schedule_meeting("Helen", meeting_time, meeting_time))
            if meeting_time >= constraints["Sandra"]["start_time"] and meeting_time <= constraints["Sandra"]["end_time"]:
                itinerary.append(schedule_meeting("Sandra", meeting_time, meeting_time))
            if meeting_time >= constraints["Mary"]["start_time"] and meeting_time <= constraints["Mary"]["end_time"]:
                itinerary.append(schedule_meeting("Mary", meeting_time, meeting_time))
            if meeting_time >= constraints["Deborah"]["start_time"] and meeting_time <= constraints["Deborah"]["end_time"]:
                itinerary.append(schedule_meeting("Deborah", meeting_time, meeting_time))
            if meeting_time >= constraints["Elizabeth"]["start_time"] and meeting_time <= constraints["Elizabeth"]["end_time"]:
                itinerary.append(schedule_meeting("Elizabeth", meeting_time, meeting_time))
    
    # Remove duplicates and sort by start time
    itinerary = list(set(itinerary))
    itinerary.sort(key=lambda x: x["start_time"])
    
    return itinerary

def optimize_itinerary(itinerary):
    optimized_itinerary = []
    current_location = "Mission District"
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