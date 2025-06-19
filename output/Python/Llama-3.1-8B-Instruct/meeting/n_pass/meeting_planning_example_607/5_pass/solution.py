import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    "Sunset District": {
        "Russian Hill": 24,
        "The Castro": 17,
        "Richmond District": 12,
        "Marina District": 21,
        "North Beach": 29,
        "Union Square": 30,
        "Golden Gate Park": 11
    },
    "Russian Hill": {
        "Sunset District": 23,
        "The Castro": 21,
        "Richmond District": 14,
        "Marina District": 7,
        "North Beach": 5,
        "Union Square": 11,
        "Golden Gate Park": 21
    },
    "The Castro": {
        "Sunset District": 17,
        "Russian Hill": 18,
        "Richmond District": 16,
        "Marina District": 21,
        "North Beach": 20,
        "Union Square": 19,
        "Golden Gate Park": 11
    },
    "Richmond District": {
        "Sunset District": 11,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "North Beach": 17,
        "Union Square": 21,
        "Golden Gate Park": 9
    },
    "Marina District": {
        "Sunset District": 19,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "North Beach": 11,
        "Union Square": 16,
        "Golden Gate Park": 18
    },
    "North Beach": {
        "Sunset District": 27,
        "Russian Hill": 4,
        "The Castro": 22,
        "Richmond District": 18,
        "Marina District": 9,
        "Union Square": 7,
        "Golden Gate Park": 22
    },
    "Union Square": {
        "Sunset District": 26,
        "Russian Hill": 13,
        "The Castro": 19,
        "Richmond District": 20,
        "Marina District": 18,
        "North Beach": 10,
        "Golden Gate Park": 22
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Russian Hill": 19,
        "The Castro": 13,
        "Richmond District": 7,
        "Marina District": 16,
        "North Beach": 24,
        "Union Square": 22
    }
}

# Constraints
constraints = {
    "Karen": (datetime(2024, 7, 26, 20, 45), datetime(2024, 7, 26, 21, 45)),
    "Jessica": (datetime(2024, 7, 26, 15, 45), datetime(2024, 7, 26, 19, 30)),
    "Matthew": (datetime(2024, 7, 26, 7, 30), datetime(2024, 7, 26, 15, 15)),
    "Michelle": (datetime(2024, 7, 26, 10, 30), datetime(2024, 7, 26, 18, 45)),
    "Carol": (datetime(2024, 7, 26, 12, 0), datetime(2024, 7, 26, 17, 0)),
    "Stephanie": (datetime(2024, 7, 26, 10, 45), datetime(2024, 7, 26, 14, 15)),
    "Linda": (datetime(2024, 7, 26, 10, 45), datetime(2024, 7, 26, 22, 0))
}

def calculate_travel_time(start, end, location):
    start_time = datetime.strptime(start, "%H:%M")
    travel_time = travel_distances["Sunset District"][location]
    travel_time_minutes = travel_time
    arrival_time = start_time + timedelta(minutes=travel_time_minutes)
    return arrival_time.strftime("%H:%M")

def calculate_meeting_duration(start, end):
    start_time = datetime.strptime(start, "%H:%M")
    end_time = datetime.strptime(end, "%H:%M")
    return (end_time - start_time).total_seconds() / 60

def schedule_meetings(constraints):
    schedule = []
    start_time = datetime.strptime("09:00", "%H:%M")
    locations = {
        "Karen": "Russian Hill",
        "Jessica": "The Castro",
        "Matthew": "Richmond District",
        "Michelle": "Marina District",
        "Carol": "North Beach",
        "Stephanie": "Union Square",
        "Linda": "Golden Gate Park"
    }
    
    for person, times in constraints.items():
        start, end = times
        arrival_time = calculate_travel_time("09:00", start.strftime("%H:%M"), locations[person])
        
        if arrival_time <= end.strftime("%H:%M"):
            schedule.append({
                "action": "travel",
                "location": locations[person],
                "person": person,
                "start_time": arrival_time,
                "end_time": start.strftime("%H:%M")
            })
            
        if arrival_time <= start.strftime("%H:%M"):
            schedule.append({
                "action": "wait",
                "location": locations[person],
                "person": person,
                "start_time": arrival_time,
                "end_time": start.strftime("%H:%M")
            })
            
        meeting_duration = calculate_meeting_duration(start.strftime("%H:%M"), end.strftime("%H:%M"))
        
        if meeting_duration >= 60 and person!= "Matthew":
            schedule.append({
                "action": "meet",
                "location": locations[person],
                "person": person,
                "start_time": start.strftime("%H:%M"),
                "end_time": end.strftime("%H:%M")
            })
            
    # Adjust the arrival time of Linda at Golden Gate Park
    linda_schedule = [item for item in schedule if item['person'] == 'Linda']
    if linda_schedule:
        linda_travel_time = travel_distances["Marina District"]["Golden Gate Park"]
        linda_arrival_time = datetime.strptime(linda_schedule[0]['end_time'], "%H:%M") + timedelta(minutes=linda_travel_time)
        linda_schedule[0]['end_time'] = linda_arrival_time.strftime("%H:%M")
        
    return schedule

def main():
    schedule = schedule_meetings(constraints)
    itinerary = {
        "itinerary": schedule
    }
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()