import json
from datetime import datetime, timedelta
import itertools

# Define travel distances in minutes
travel_distances = {
    "Financial District": {
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Bayview": 19,
        "Haight-Ashbury": 19,
        "Russian Hill": 11,
        "The Castro": 20,
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Sunset District": 30
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Presidio": 17,
        "Bayview": 26,
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "The Castro": 27,
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Sunset District": 27
    },
    "Presidio": {
        "Financial District": 23,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Haight-Ashbury": 15,
        "Russian Hill": 14,
        "The Castro": 21,
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Sunset District": 15
    },
    "Bayview": {
        "Financial District": 19,
        "Fisherman's Wharf": 25,
        "Presidio": 32,
        "Haight-Ashbury": 19,
        "Russian Hill": 23,
        "The Castro": 19,
        "Marina District": 27,
        "Richmond District": 25,
        "Union Square": 18,
        "Sunset District": 23
    },
    "Haight-Ashbury": {
        "Financial District": 21,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Bayview": 18,
        "Russian Hill": 17,
        "The Castro": 6,
        "Marina District": 17,
        "Richmond District": 10,
        "Union Square": 19,
        "Sunset District": 15
    },
    "Russian Hill": {
        "Financial District": 11,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Bayview": 23,
        "Haight-Ashbury": 17,
        "The Castro": 21,
        "Marina District": 7,
        "Richmond District": 14,
        "Union Square": 10,
        "Sunset District": 23
    },
    "The Castro": {
        "Financial District": 21,
        "Fisherman's Wharf": 24,
        "Presidio": 20,
        "Bayview": 19,
        "Haight-Ashbury": 6,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Union Square": 19,
        "Sunset District": 17
    },
    "Marina District": {
        "Financial District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Bayview": 27,
        "Haight-Ashbury": 16,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "Union Square": 16,
        "Sunset District": 19
    },
    "Richmond District": {
        "Financial District": 22,
        "Fisherman's Wharf": 18,
        "Presidio": 7,
        "Bayview": 27,
        "Haight-Ashbury": 10,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "Union Square": 21,
        "Sunset District": 11
    },
    "Union Square": {
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Bayview": 15,
        "Haight-Ashbury": 18,
        "Russian Hill": 13,
        "The Castro": 17,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27
    },
    "Sunset District": {
        "Financial District": 30,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Russian Hill": 24,
        "The Castro": 17,
        "Marina District": 21,
        "Richmond District": 12,
        "Union Square": 30
    }
}

# Define meeting constraints
constraints = {
    "Mark": {"location": "Fisherman's Wharf", "start_time": "08:15", "end_time": "10:00", "duration": 30},
    "Stephanie": {"location": "Presidio", "start_time": "12:15", "end_time": "15:00", "duration": 75},
    "Betty": {"location": "Bayview", "start_time": "07:15", "end_time": "20:30", "duration": 15},
    "Lisa": {"location": "Haight-Ashbury", "start_time": "15:30", "end_time": "18:30", "duration": 45},
    "William": {"location": "Russian Hill", "start_time": "18:45", "end_time": "20:00", "duration": 60},
    "Brian": {"location": "The Castro", "start_time": "09:15", "end_time": "13:15", "duration": 30},
    "Joseph": {"location": "Marina District", "start_time": "10:45", "end_time": "15:00", "duration": 90},
    "Ashley": {"location": "Richmond District", "start_time": "09:45", "end_time": "11:15", "duration": 45},
    "Patricia": {"location": "Union Square", "start_time": "16:30", "end_time": "20:00", "duration": 120},
    "Karen": {"location": "Sunset District", "start_time": "16:30", "end_time": "22:00", "duration": 105}
}

def calculate_travel_time(start_location, end_location):
    if start_location == "Financial District":
        return travel_distances["Financial District"][end_location]
    elif start_location == "Fisherman's Wharf":
        return travel_distances["Fisherman's Wharf"][end_location]
    elif start_location == "Presidio":
        return travel_distances["Presidio"][end_location]
    elif start_location == "Bayview":
        return travel_distances["Bayview"][end_location]
    elif start_location == "Haight-Ashbury":
        return travel_distances["Haight-Ashbury"][end_location]
    elif start_location == "Russian Hill":
        return travel_distances["Russian Hill"][end_location]
    elif start_location == "The Castro":
        return travel_distances["The Castro"][end_location]
    elif start_location == "Marina District":
        return travel_distances["Marina District"][end_location]
    elif start_location == "Richmond District":
        return travel_distances["Richmond District"][end_location]
    elif start_location == "Union Square":
        return travel_distances["Union Square"][end_location]
    elif start_location == "Sunset District":
        return travel_distances["Sunset District"][end_location]

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
    start_location = "Financial District"
    itinerary = []
    
    # Generate all possible meeting times
    for hour in range(9, 22):
        for minute in range(0, 60):
            meeting_time = f"{hour:02d}:{minute:02d}"
            if meeting_time >= constraints["Mark"]["start_time"] and meeting_time <= constraints["Mark"]["end_time"]:
                itinerary.append(schedule_meeting("Mark", meeting_time, meeting_time))
            if meeting_time >= constraints["Stephanie"]["start_time"] and meeting_time <= constraints["Stephanie"]["end_time"]:
                itinerary.append(schedule_meeting("Stephanie", meeting_time, meeting_time))
            if meeting_time >= constraints["Betty"]["start_time"] and meeting_time <= constraints["Betty"]["end_time"]:
                itinerary.append(schedule_meeting("Betty", meeting_time, meeting_time))
            if meeting_time >= constraints["Lisa"]["start_time"] and meeting_time <= constraints["Lisa"]["end_time"]:
                itinerary.append(schedule_meeting("Lisa", meeting_time, meeting_time))
            if meeting_time >= constraints["William"]["start_time"] and meeting_time <= constraints["William"]["end_time"]:
                itinerary.append(schedule_meeting("William", meeting_time, meeting_time))
            if meeting_time >= constraints["Brian"]["start_time"] and meeting_time <= constraints["Brian"]["end_time"]:
                itinerary.append(schedule_meeting("Brian", meeting_time, meeting_time))
            if meeting_time >= constraints["Joseph"]["start_time"] and meeting_time <= constraints["Joseph"]["end_time"]:
                itinerary.append(schedule_meeting("Joseph", meeting_time, meeting_time))
            if meeting_time >= constraints["Ashley"]["start_time"] and meeting_time <= constraints["Ashley"]["end_time"]:
                itinerary.append(schedule_meeting("Ashley", meeting_time, meeting_time))
            if meeting_time >= constraints["Patricia"]["start_time"] and meeting_time <= constraints["Patricia"]["end_time"]:
                itinerary.append(schedule_meeting("Patricia", meeting_time, meeting_time))
            if meeting_time >= constraints["Karen"]["start_time"] and meeting_time <= constraints["Karen"]["end_time"]:
                itinerary.append(schedule_meeting("Karen", meeting_time, meeting_time))
    
    # Remove duplicates and sort by start time
    itinerary = list(set(itinerary))
    itinerary.sort(key=lambda x: x["start_time"])
    
    return itinerary

def optimize_itinerary(itinerary):
    optimized_itinerary = []
    current_location = "Financial District"
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