import json
from datetime import datetime, timedelta
import itertools

# Define travel distances in minutes
travel_distances = {
    "Embarcadero": {
        "Richmond District": 21,
        "Union Square": 10,
        "Financial District": 5,
        "Pacific Heights": 11,
        "Nob Hill": 10,
        "Bayview": 21
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Union Square": 21,
        "Financial District": 22,
        "Pacific Heights": 10,
        "Nob Hill": 17,
        "Bayview": 26
    },
    "Union Square": {
        "Embarcadero": 11,
        "Richmond District": 20,
        "Financial District": 9,
        "Pacific Heights": 15,
        "Nob Hill": 9,
        "Bayview": 15
    },
    "Financial District": {
        "Embarcadero": 4,
        "Richmond District": 21,
        "Union Square": 9,
        "Pacific Heights": 13,
        "Nob Hill": 8,
        "Bayview": 19
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Richmond District": 12,
        "Union Square": 12,
        "Financial District": 13,
        "Nob Hill": 8,
        "Bayview": 22
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Richmond District": 14,
        "Union Square": 7,
        "Financial District": 9,
        "Pacific Heights": 8,
        "Bayview": 19
    },
    "Bayview": {
        "Embarcadero": 19,
        "Richmond District": 25,
        "Union Square": 17,
        "Financial District": 19,
        "Pacific Heights": 23,
        "Nob Hill": 20
    }
}

# Define meeting constraints
constraints = {
    "Kenneth": {"location": "Richmond District", "start_time": "21:15", "end_time": "22:00", "duration": 30},
    "Lisa": {"location": "Union Square", "start_time": "09:00", "end_time": "16:30", "duration": 45},
    "Joshua": {"location": "Financial District", "start_time": "12:00", "end_time": "15:15", "duration": 15},
    "Nancy": {"location": "Pacific Heights", "start_time": "08:00", "end_time": "11:30", "duration": 90},
    "Andrew": {"location": "Nob Hill", "start_time": "11:30", "end_time": "20:15", "duration": 60},
    "John": {"location": "Bayview", "start_time": "16:45", "end_time": "21:30", "duration": 75}
}

def calculate_travel_time(start_location, end_location):
    if start_location == "Embarcadero":
        return travel_distances["Embarcadero"][end_location]
    elif start_location == "Richmond District":
        return travel_distances["Richmond District"][end_location]
    elif start_location == "Union Square":
        return travel_distances["Union Square"][end_location]
    elif start_location == "Financial District":
        return travel_distances["Financial District"][end_location]
    elif start_location == "Pacific Heights":
        return travel_distances["Pacific Heights"][end_location]
    elif start_location == "Nob Hill":
        return travel_distances["Nob Hill"][end_location]
    elif start_location == "Bayview":
        return travel_distances["Bayview"][end_location]

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
    start_location = "Embarcadero"
    itinerary = []
    
    # Generate all possible meeting times
    for hour in range(9, 22):
        for minute in range(0, 60):
            meeting_time = f"{hour:02d}:{minute:02d}"
            if meeting_time >= constraints["Kenneth"]["start_time"] and meeting_time <= constraints["Kenneth"]["end_time"]:
                itinerary.append(schedule_meeting("Kenneth", meeting_time, meeting_time))
            if meeting_time >= constraints["Lisa"]["start_time"] and meeting_time <= constraints["Lisa"]["end_time"]:
                itinerary.append(schedule_meeting("Lisa", meeting_time, meeting_time))
            if meeting_time >= constraints["Joshua"]["start_time"] and meeting_time <= constraints["Joshua"]["end_time"]:
                itinerary.append(schedule_meeting("Joshua", meeting_time, meeting_time))
            if meeting_time >= constraints["Nancy"]["start_time"] and meeting_time <= constraints["Nancy"]["end_time"]:
                itinerary.append(schedule_meeting("Nancy", meeting_time, meeting_time))
            if meeting_time >= constraints["Andrew"]["start_time"] and meeting_time <= constraints["Andrew"]["end_time"]:
                itinerary.append(schedule_meeting("Andrew", meeting_time, meeting_time))
            if meeting_time >= constraints["John"]["start_time"] and meeting_time <= constraints["John"]["end_time"]:
                itinerary.append(schedule_meeting("John", meeting_time, meeting_time))
    
    # Remove duplicates and sort by start time
    itinerary = list(set(itinerary))
    itinerary.sort(key=lambda x: x["start_time"])
    
    return itinerary

def optimize_itinerary(itinerary):
    optimized_itinerary = []
    current_location = "Embarcadero"
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