import json
from datetime import datetime, timedelta

class Meeting:
    def __init__(self, name, location, start_time, end_time, duration):
        self.name = name
        self.location = location
        self.start_time = datetime.strptime(start_time, "%H:%M")  # Convert start_time to datetime object
        self.end_time = datetime.strptime(end_time, "%H:%M")  # Convert end_time to datetime object
        self.duration = duration

class Person:
    def __init__(self, name, location, start_time, end_time, duration):
        self.name = name
        self.location = location
        self.start_time = datetime.strptime(start_time, "%H:%M")  # Convert start_time to datetime object
        self.end_time = datetime.strptime(end_time, "%H:%M")  # Convert end_time to datetime object
        self.duration = duration

class Location:
    def __init__(self, name):
        self.name = name
        self.travel_times = {
            "Pacific Heights": {"Nob Hill": 8, "Russian Hill": 7, "The Castro": 16, "Sunset District": 21, "Haight-Ashbury": 11},
            "Nob Hill": {"Pacific Heights": 8, "Russian Hill": 5, "The Castro": 17, "Sunset District": 25, "Haight-Ashbury": 13},
            "Russian Hill": {"Pacific Heights": 7, "Nob Hill": 5, "The Castro": 21, "Sunset District": 23, "Haight-Ashbury": 17},
            "The Castro": {"Pacific Heights": 16, "Nob Hill": 17, "Russian Hill": 21, "Sunset District": 17, "Haight-Ashbury": 6},
            "Sunset District": {"Pacific Heights": 21, "Nob Hill": 25, "Russian Hill": 23, "The Castro": 17, "Haight-Ashbury": 15},
            "Haight-Ashbury": {"Pacific Heights": 11, "Nob Hill": 13, "Russian Hill": 17, "The Castro": 6, "Sunset District": 15}
        }

def compute_travel_time(start_location, end_location):
    if start_location not in Location(None).travel_times or end_location not in Location(None).travel_times[start_location]:
        return 0
    return Location(None).travel_times[start_location][end_location]

def compute_meeting_schedule():
    start_time = datetime.strptime("09:00", "%H:%M")
    meetings = [
        Person("Ronald", "Nob Hill", "10:00", "17:00", 105),
        Person("Sarah", "Russian Hill", "07:15", "09:30", 45),
        Person("Helen", "The Castro", "13:30", "17:00", 120),
        Person("Joshua", "Sunset District", "14:15", "19:30", 90),
        Person("Margaret", "Haight-Ashbury", "10:15", "22:00", 60)
    ]

    schedule = []
    current_time = start_time
    current_location = "Pacific Heights"

    for person in meetings:
        if person.start_time < current_time:
            current_time = person.start_time
            current_location = person.location

        while current_time < person.start_time:
            travel_time = compute_travel_time(current_location, person.location)
            current_time += timedelta(minutes=travel_time + 30)

        schedule.append({
            "action": "meet",
            "location": person.location,
            "person": person.name,
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + timedelta(minutes=person.duration)).strftime("%H:%M")
        })

        current_time += timedelta(minutes=person.duration + compute_travel_time(person.location, "Pacific Heights"))

    return {"itinerary": schedule}

def main():
    schedule = compute_meeting_schedule()
    print(json.dumps(schedule, indent=4))

if __name__ == "__main__":
    main()