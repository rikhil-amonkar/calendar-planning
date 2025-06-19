import json
from datetime import datetime, timedelta

class MeetingScheduler:
    def __init__(self, travel_times, constraints):
        self.travel_times = travel_times
        self.constraints = constraints

    def compute_travel_time(self, start_location, end_location):
        # Retrieve travel time in both directions and use the shorter one
        travel_time_forward = self.travel_times.get(f"{start_location}-{end_location}", float('inf'))
        travel_time_backward = self.travel_times.get(f"{end_location}-{start_location}", float('inf'))
        return min(travel_time_forward, travel_time_backward)

    def compute_meeting_time(self, start_time, end_time, travel_time):
        return (end_time - start_time).total_seconds() / 60

    def find_optimal_meetings(self, start_time, end_time, person, location, min_meeting_time):
        optimal_meetings = []
        for i in range(int((end_time - start_time).total_seconds() / 60 / min_meeting_time) + 1):
            meeting_time = start_time + timedelta(minutes=i * min_meeting_time)
            if meeting_time > end_time:
                break
            travel_time = self.compute_travel_time(location, self.constraints[person]["location"])
            end_time = meeting_time + timedelta(minutes=travel_time)
            if end_time <= self.constraints[person]["end_time"]:
                optimal_meetings.append({
                    "action": "meet",
                    "location": self.constraints[person]["location"],
                    "person": person,
                    "start_time": meeting_time.strftime("%H:%M"),
                    "end_time": end_time.strftime("%H:%M")
                })
        return optimal_meetings

    def compute_optimal_schedule(self):
        start_time = datetime.strptime("09:00", "%H:%M")
        schedule = []

        # Sarah
        sarah_meetings = self.find_optimal_meetings(start_time, self.constraints["Sarah"]["end_time"], "Sarah", self.constraints["Sarah"]["location"], self.constraints["Sarah"]["min_meeting_time"])
        if sarah_meetings:
            schedule.extend(sarah_meetings)
            start_time = datetime.strptime(max(meeting["start_time"] for meeting in sarah_meetings), "%H:%M")

        # Mary
        mary_meetings = self.find_optimal_meetings(start_time, self.constraints["Mary"]["end_time"], "Mary", self.constraints["Mary"]["location"], self.constraints["Mary"]["min_meeting_time"])
        if mary_meetings:
            schedule.extend(mary_meetings)
            start_time = datetime.strptime(max(meeting["start_time"] for meeting in mary_meetings), "%H:%M")

        # Thomas
        thomas_meetings = self.find_optimal_meetings(start_time, self.constraints["Thomas"]["end_time"], "Thomas", self.constraints["Thomas"]["location"], self.constraints["Thomas"]["min_meeting_time"])
        if thomas_meetings:
            schedule.extend(thomas_meetings)
            start_time = datetime.strptime(max(meeting["start_time"] for meeting in thomas_meetings), "%H:%M")

        # Helen
        helen_meetings = self.find_optimal_meetings(start_time, self.constraints["Helen"]["end_time"], "Helen", self.constraints["Helen"]["location"], self.constraints["Helen"]["min_meeting_time"])
        if helen_meetings:
            schedule.extend(helen_meetings)

        # Sort schedule by start time
        schedule.sort(key=lambda x: x['start_time'])

        return {"itinerary": schedule}

def main():
    travel_times = {
        "Haight-Ashbury-Fisherman's Wharf": 23,
        "Haight-Ashbury-Richmond District": 10,
        "Haight-Ashbury-Mission District": 11,
        "Haight-Ashbury-Bayview": 18,
        "Fisherman's Wharf-Haight-Ashbury": 22,
        "Fisherman's Wharf-Richmond District": 18,
        "Fisherman's Wharf-Mission District": 22,
        "Fisherman's Wharf-Bayview": 26,
        "Richmond District-Haight-Ashbury": 10,
        "Richmond District-Fisherman's Wharf": 18,
        "Richmond District-Mission District": 20,
        "Richmond District-Bayview": 26,
        "Mission District-Haight-Ashbury": 12,
        "Mission District-Fisherman's Wharf": 22,
        "Mission District-Richmond District": 20,
        "Mission District-Bayview": 15,
        "Bayview-Haight-Ashbury": 19,
        "Bayview-Fisherman's Wharf": 25,
        "Bayview-Richmond District": 25,
        "Bayview-Mission District": 13
    }

    constraints = {
        "start_location": "Haight-Ashbury",
        "Sarah": {"location": "Fisherman's Wharf", "start_time": datetime.strptime("14:45", "%H:%M"), "end_time": datetime.strptime("17:30", "%H:%M"), "min_meeting_time": 105},
        "Mary": {"location": "Richmond District", "start_time": datetime.strptime("13:00", "%H:%M"), "end_time": datetime.strptime("19:15", "%H:%M"), "min_meeting_time": 75},
        "Helen": {"location": "Mission District", "start_time": datetime.strptime("21:45", "%H:%M"), "end_time": datetime.strptime("22:30", "%H:%M"), "min_meeting_time": 30},
        "Thomas": {"location": "Bayview", "start_time": datetime.strptime("15:15", "%H:%M"), "end_time": datetime.strptime("18:45", "%H:%M"), "min_meeting_time": 120}
    }

    scheduler = MeetingScheduler(travel_times, constraints)
    schedule = scheduler.compute_optimal_schedule()
    print(json.dumps(schedule, indent=4))

if __name__ == "__main__":
    main()