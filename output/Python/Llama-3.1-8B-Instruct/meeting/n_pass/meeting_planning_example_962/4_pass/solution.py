import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "The Castro": {
        "Marina District": 22,
        "Presidio": 20,
        "North Beach": 20,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Sunset District": 17
    },
    "Marina District": {
        "The Castro": 22,
        "Presidio": 10,
        "North Beach": 11,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Sunset District": 19
    },
    "Presidio": {
        "The Castro": 21,
        "Marina District": 11,
        "North Beach": 18,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Sunset District": 15
    },
    "North Beach": {
        "The Castro": 23,
        "Marina District": 9,
        "Presidio": 17,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Alamo Square": 16,
        "Financial District": 8,
        "Sunset District": 27
    },
    "Embarcadero": {
        "The Castro": 25,
        "Marina District": 12,
        "Presidio": 20,
        "North Beach": 5,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Alamo Square": 19,
        "Financial District": 5,
        "Sunset District": 30
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Marina District": 17,
        "Presidio": 15,
        "North Beach": 19,
        "Embarcadero": 20,
        "Golden Gate Park": 7,
        "Richmond District": 10,
        "Alamo Square": 5,
        "Financial District": 21,
        "Sunset District": 15
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Marina District": 16,
        "Presidio": 11,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Alamo Square": 9,
        "Financial District": 26,
        "Sunset District": 10
    },
    "Richmond District": {
        "The Castro": 16,
        "Marina District": 9,
        "Presidio": 7,
        "North Beach": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Golden Gate Park": 9,
        "Alamo Square": 13,
        "Financial District": 22,
        "Sunset District": 11
    },
    "Alamo Square": {
        "The Castro": 8,
        "Marina District": 15,
        "Presidio": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Financial District": 17,
        "Sunset District": 16
    },
    "Financial District": {
        "The Castro": 20,
        "Marina District": 15,
        "Presidio": 22,
        "North Beach": 7,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Sunset District": 30
    },
    "Sunset District": {
        "The Castro": 17,
        "Marina District": 21,
        "Presidio": 16,
        "North Beach": 28,
        "Embarcadero": 30,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Richmond District": 12,
        "Alamo Square": 17,
        "Financial District": 30
    }
}

# Constraints
constraints = {
    "Elizabeth": {"start_time": "19:00", "end_time": "20:45", "min_time": 105},
    "Joshua": {"start_time": "8:30", "end_time": "13:15", "min_time": 105},
    "Timothy": {"start_time": "19:45", "end_time": "22:00", "min_time": 90},
    "David": {"start_time": "10:45", "end_time": "12:30", "min_time": 30},
    "Kimberly": {"start_time": "16:45", "end_time": "21:30", "min_time": 75},
    "Lisa": {"start_time": "17:30", "end_time": "21:45", "min_time": 45},
    "Ronald": {"start_time": "8:00", "end_time": "9:30", "min_time": 90},
    "Stephanie": {"start_time": "15:30", "end_time": "16:30", "min_time": 30},
    "Helen": {"start_time": "17:30", "end_time": "18:30", "min_time": 45},
    "Laura": {"start_time": "17:45", "end_time": "21:15", "min_time": 90}
}

def calculate_travel_time(current_location, person):
    # Return the travel distance from the current location to the person's start location
    return travel_distances[current_location][person]

def is_valid_schedule(schedule):
    for person in constraints:
        start_time = datetime.strptime(constraints[person]["start_time"], "%H:%M")
        end_time = datetime.strptime(constraints[person]["end_time"], "%H:%M")
        min_time = constraints[person]["min_time"]
        for meeting in schedule:
            if meeting["person"] == person:
                meeting_start_time = datetime.strptime(meeting["start_time"], "%H:%M")
                meeting_end_time = datetime.strptime(meeting["end_time"], "%H:%M")
                if meeting_start_time < start_time or meeting_end_time > end_time:
                    return False
                if meeting_start_time < end_time and meeting_end_time > start_time:
                    if meeting_end_time - meeting_start_time < timedelta(minutes=min_time):
                        return False
    return True

def find_optimal_schedule():
    schedule = []
    current_location = "The Castro"
    start_time = "09:00"
    end_time = datetime.strptime(start_time, "%H:%M") + timedelta(hours=12)
    while datetime.strptime(start_time, "%H:%M") < end_time:
        for person in constraints:
            start_person_time = datetime.strptime(constraints[person]["start_time"], "%H:%M")
            end_person_time = datetime.strptime(constraints[person]["end_time"], "%H:%M")
            min_time = constraints[person]["min_time"]
            if start_person_time <= datetime.strptime(start_time, "%H:%M") < end_person_time:
                travel_time = calculate_travel_time(current_location, person)
                meeting_start_time = datetime.strptime(start_time, "%H:%M") + timedelta(minutes=travel_time)
                meeting_end_time = meeting_start_time + timedelta(minutes=min_time)
                if meeting_end_time <= end_time:
                    schedule.append({"action": "meet", "location": current_location, "person": person, "start_time": meeting_start_time.strftime("%H:%M"), "end_time": meeting_end_time.strftime("%H:%M")})
                    current_location = person
                    start_time = meeting_end_time.strftime("%H:%M")
                    break
        else:
            current_location = "The Castro"
            start_time = datetime.strptime(start_time, "%H:%M").strftime("%H:%M")
    return schedule

def main():
    schedule = find_optimal_schedule()
    if is_valid_schedule(schedule):
        print(json.dumps({"itinerary": schedule}, indent=4))
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()