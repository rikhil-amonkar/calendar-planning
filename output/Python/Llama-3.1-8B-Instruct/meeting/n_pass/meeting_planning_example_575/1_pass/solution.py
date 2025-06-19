import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    "The Castro": {
        "Presidio": 20,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Golden Gate Park": 11,
        "Russian Hill": 18,
    },
    "Presidio": {
        "The Castro": 21,
        "Sunset District": 15,
        "Haight-Ashbury": 15,
        "Mission District": 26,
        "Golden Gate Park": 12,
        "Russian Hill": 14,
    },
    "Sunset District": {
        "The Castro": 17,
        "Presidio": 16,
        "Haight-Ashbury": 15,
        "Mission District": 24,
        "Golden Gate Park": 11,
        "Russian Hill": 24,
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Presidio": 15,
        "Sunset District": 15,
        "Mission District": 11,
        "Golden Gate Park": 7,
        "Russian Hill": 17,
    },
    "Mission District": {
        "The Castro": 7,
        "Presidio": 25,
        "Sunset District": 24,
        "Haight-Ashbury": 12,
        "Golden Gate Park": 17,
        "Russian Hill": 15,
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Presidio": 11,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Russian Hill": 19,
    },
    "Russian Hill": {
        "The Castro": 21,
        "Presidio": 14,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Golden Gate Park": 21,
    },
}

# Define meeting constraints
meeting_constraints = {
    "Rebecca": {"start_time": "18:15", "end_time": "20:45", "min_time": 60},
    "Linda": {"start_time": "15:30", "end_time": "19:45", "min_time": 30},
    "Elizabeth": {"start_time": "17:15", "end_time": "19:30", "min_time": 105},
    "William": {"start_time": "13:15", "end_time": "19:30", "min_time": 30},
    "Robert": {"start_time": "14:15", "end_time": "21:30", "min_time": 45},
    "Mark": {"start_time": "10:00", "end_time": "21:15", "min_time": 75},
}

def calculate_travel_time(location1, location2):
    return travel_distances[location1][location2]

def is_valid_meeting(person, start_time, end_time):
    meeting_start_time = datetime.strptime(start_time, "%H:%M")
    meeting_end_time = datetime.strptime(end_time, "%H:%M")
    return (meeting_start_time >= datetime.strptime(meeting_constraints[person]["start_time"], "%H:%M") and
            meeting_end_time <= datetime.strptime(meeting_constraints[person]["end_time"], "%H:%M"))

def calculate_meeting_duration(start_time, end_time):
    return (datetime.strptime(end_time, "%H:%M") - datetime.strptime(start_time, "%H:%M")).total_seconds() / 60

def compute_optimal_schedule():
    schedule = []
    start_time = "09:00"
    current_location = "The Castro"

    for person, constraint in meeting_constraints.items():
        start_time_str = constraint["start_time"]
        end_time_str = constraint["end_time"]
        min_time = constraint["min_time"]

        # Check if meeting is possible
        if is_valid_meeting(person, start_time_str, end_time_str):
            travel_time = calculate_travel_time(current_location, person)
            start_time = datetime.strptime(start_time, "%H:%M") + timedelta(minutes=travel_time)
            start_time_str = start_time.strftime("%H:%M")

            # Calculate meeting duration
            meeting_duration = calculate_meeting_duration(start_time_str, end_time_str)
            if meeting_duration >= min_time:
                schedule.append({
                    "action": "meet",
                    "location": person,
                    "person": person,
                    "start_time": start_time_str,
                    "end_time": end_time_str,
                })

                # Update current location
                current_location = person

                # Update start time
                start_time = datetime.strptime(end_time_str, "%H:%M") + timedelta(minutes=1)

    return schedule

def main():
    schedule = compute_optimal_schedule()
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()