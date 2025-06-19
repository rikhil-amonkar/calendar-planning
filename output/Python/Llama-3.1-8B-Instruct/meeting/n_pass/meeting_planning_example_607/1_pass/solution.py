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
    end_time = datetime.strptime(end, "%H:%M")
    travel_time = travel_distances["Sunset District"][location]
    travel_time_minutes = travel_time // 60
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
        arrival_time = calculate_travel_time("09:00", start, locations[person])
        meeting_duration = calculate_meeting_duration(start, end)
        
        if meeting_duration >= 60:
            schedule.append({
                "action": "meet",
                "location": locations[person],
                "person": person,
                "start_time": start,
                "end_time": end
            })
            
        if arrival_time <= end:
            schedule.append({
                "action": "travel",
                "location": locations[person],
                "person": person,
                "start_time": arrival_time,
                "end_time": start
            })
            
        if arrival_time <= start:
            schedule.append({
                "action": "wait",
                "location": locations[person],
                "person": person,
                "start_time": arrival_time,
                "end_time": start
            })
            
        if meeting_duration >= 75 and person == "Michelle":
            schedule.append({
                "action": "meet",
                "location": locations[person],
                "person": person,
                "start_time": start,
                "end_time": end
            })
            
        if meeting_duration >= 90 and person in ["Carol", "Linda"]:
            schedule.append({
                "action": "meet",
                "location": locations[person],
                "person": person,
                "start_time": start,
                "end_time": end
            })
            
        if meeting_duration >= 15 and person == "Matthew":
            schedule.append({
                "action": "meet",
                "location": locations[person],
                "person": person,
                "start_time": start,
                "end_time": end
            })
            
        if meeting_duration >= 30 and person == "Stephanie":
            schedule.append({
                "action": "meet",
                "location": locations[person],
                "person": person,
                "start_time": start,
                "end_time": end
            })
            
    return schedule

def main():
    schedule = schedule_meetings(constraints)
    itinerary = {
        "itinerary": schedule
    }
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()