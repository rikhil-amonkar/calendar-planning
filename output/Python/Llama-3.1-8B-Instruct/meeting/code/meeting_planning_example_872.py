import json
from datetime import datetime, timedelta
import itertools

# Define travel distances in minutes
travel_distances = {
    "Presidio": {
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "Russian Hill": 14,
        "North Beach": 18,
        "Chinatown": 21,
        "Union Square": 22,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11
    },
    "Haight-Ashbury": {
        "Presidio": 15,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "North Beach": 19,
        "Chinatown": 19,
        "Union Square": 19,
        "Embarcadero": 20,
        "Financial District": 21,
        "Marina District": 17
    },
    "Nob Hill": {
        "Presidio": 17,
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "North Beach": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Embarcadero": 9,
        "Financial District": 9,
        "Marina District": 11
    },
    "Russian Hill": {
        "Presidio": 14,
        "Haight-Ashbury": 17,
        "Nob Hill": 5,
        "North Beach": 5,
        "Chinatown": 9,
        "Union Square": 10,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7
    },
    "North Beach": {
        "Presidio": 17,
        "Haight-Ashbury": 18,
        "Nob Hill": 7,
        "Russian Hill": 4,
        "Chinatown": 6,
        "Union Square": 7,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9
    },
    "Chinatown": {
        "Presidio": 19,
        "Haight-Ashbury": 19,
        "Nob Hill": 9,
        "Russian Hill": 7,
        "North Beach": 3,
        "Union Square": 7,
        "Embarcadero": 5,
        "Financial District": 5,
        "Marina District": 12
    },
    "Union Square": {
        "Presidio": 24,
        "Haight-Ashbury": 18,
        "Nob Hill": 9,
        "Russian Hill": 13,
        "North Beach": 10,
        "Chinatown": 7,
        "Embarcadero": 11,
        "Financial District": 9,
        "Marina District": 18
    },
    "Embarcadero": {
        "Presidio": 20,
        "Haight-Ashbury": 21,
        "Nob Hill": 10,
        "Russian Hill": 8,
        "North Beach": 5,
        "Chinatown": 7,
        "Union Square": 10,
        "Financial District": 5,
        "Marina District": 12
    },
    "Financial District": {
        "Presidio": 22,
        "Haight-Ashbury": 19,
        "Nob Hill": 8,
        "Russian Hill": 11,
        "North Beach": 7,
        "Chinatown": 5,
        "Union Square": 9,
        "Embarcadero": 4,
        "Marina District": 15
    },
    "Marina District": {
        "Presidio": 10,
        "Haight-Ashbury": 16,
        "Nob Hill": 12,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Union Square": 16,
        "Embarcadero": 14,
        "Financial District": 17
    }
}

# Define meeting constraints
constraints = {
    "Karen": {"location": "Haight-Ashbury", "start_time": "21:00", "end_time": "21:45", "duration": 45},
    "Jessica": {"location": "Nob Hill", "start_time": "13:45", "end_time": "21:00", "duration": 90},
    "Brian": {"location": "Russian Hill", "start_time": "15:30", "end_time": "21:45", "duration": 60},
    "Kenneth": {"location": "North Beach", "start_time": "09:45", "end_time": "21:00", "duration": 30},
    "Jason": {"location": "Chinatown", "start_time": "08:15", "end_time": "11:45", "duration": 75},
    "Stephanie": {"location": "Union Square", "start_time": "14:45", "end_time": "18:45", "duration": 105},
    "Kimberly": {"location": "Embarcadero", "start_time": "09:45", "end_time": "19:30", "duration": 75},
    "Steven": {"location": "Financial District", "start_time": "07:15", "end_time": "21:15", "duration": 60},
    "Mark": {"location": "Marina District", "start_time": "10:15", "end_time": "13:00", "duration": 75}
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
    start_location = "Presidio"
    itinerary = []
    
    # Generate all possible meeting times
    for hour in range(9, 21):
        for minute in range(0, 60):
            meeting_time = f"{hour:02d}:{minute:02d}"
            if meeting_time >= constraints["Karen"]["start_time"] and meeting_time <= constraints["Karen"]["end_time"]:
                itinerary.append(schedule_meeting("Karen", meeting_time, meeting_time))
            if meeting_time >= constraints["Jessica"]["start_time"] and meeting_time <= constraints["Jessica"]["end_time"]:
                itinerary.append(schedule_meeting("Jessica", meeting_time, meeting_time))
            if meeting_time >= constraints["Brian"]["start_time"] and meeting_time <= constraints["Brian"]["end_time"]:
                itinerary.append(schedule_meeting("Brian", meeting_time, meeting_time))
            if meeting_time >= constraints["Kenneth"]["start_time"] and meeting_time <= constraints["Kenneth"]["end_time"]:
                itinerary.append(schedule_meeting("Kenneth", meeting_time, meeting_time))
            if meeting_time >= constraints["Jason"]["start_time"] and meeting_time <= constraints["Jason"]["end_time"]:
                itinerary.append(schedule_meeting("Jason", meeting_time, meeting_time))
            if meeting_time >= constraints["Stephanie"]["start_time"] and meeting_time <= constraints["Stephanie"]["end_time"]:
                itinerary.append(schedule_meeting("Stephanie", meeting_time, meeting_time))
            if meeting_time >= constraints["Kimberly"]["start_time"] and meeting_time <= constraints["Kimberly"]["end_time"]:
                itinerary.append(schedule_meeting("Kimberly", meeting_time, meeting_time))
            if meeting_time >= constraints["Steven"]["start_time"] and meeting_time <= constraints["Steven"]["end_time"]:
                itinerary.append(schedule_meeting("Steven", meeting_time, meeting_time))
            if meeting_time >= constraints["Mark"]["start_time"] and meeting_time <= constraints["Mark"]["end_time"]:
                itinerary.append(schedule_meeting("Mark", meeting_time, meeting_time))
    
    # Remove duplicates and sort by start time
    itinerary = list(set(itinerary))
    itinerary.sort(key=lambda x: x["start_time"])
    
    return itinerary

def optimize_itinerary(itinerary):
    optimized_itinerary = []
    current_location = "Presidio"
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