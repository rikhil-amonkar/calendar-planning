import json
from datetime import datetime, timedelta

class MeetingPlanner:
    def __init__(self):
        self.travel_times = {
            "Sunset District to North Beach": 29,
            "Sunset District to Union Square": 30,
            "Sunset District to Alamo Square": 17,
            "North Beach to Sunset District": 27,
            "North Beach to Union Square": 7,
            "North Beach to Alamo Square": 16,
            "Union Square to Sunset District": 26,
            "Union Square to North Beach": 10,
            "Union Square to Alamo Square": 15,
            "Alamo Square to Sunset District": 16,
            "Alamo Square to North Beach": 15,
            "Alamo Square to Union Square": 14
        }
        self.constraints = {
            "Sarah": {"start_time": 16, "end_time": 18, "location": "North Beach", "min_meeting_time": 60},
            "Jeffrey": {"start_time": 15, "end_time": 22, "location": "Union Square", "min_meeting_time": 75},
            "Brian": {"start_time": 16, "end_time": 17, "location": "Alamo Square", "min_meeting_time": 75}
        }
        self.arrival_time = 9
        self.itinerary = []

    def calculate_travel_time(self, start_location, end_location):
        return self.travel_times[f"{start_location} to {end_location}"]

    def calculate_meeting_time(self, start_time, end_time, min_meeting_time):
        return max(0, end_time - start_time - min_meeting_time + 1)

    def is_valid_meeting(self, person, start_time, end_time, location):
        return (self.constraints[person]["start_time"] <= start_time <= self.constraints[person]["end_time"] and
                self.constraints[person]["location"] == location)

    def schedule_meeting(self, person, start_time, end_time, location):
        if self.is_valid_meeting(person, start_time, end_time, location):
            meeting_time = self.calculate_meeting_time(start_time, end_time, self.constraints[person]["min_meeting_time"])
            self.itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": f"{start_time // 100}:{start_time % 100:02}",
                "end_time": f"{end_time // 100}:{end_time % 100:02}"
            })
            return meeting_time
        return 0

    def compute_optimal_schedule(self):
        current_time = self.arrival_time * 100
        for person in self.constraints:
            for i in range(self.constraints[person]["start_time"] * 100, self.constraints[person]["end_time"] * 100):
                if i >= current_time:
                    travel_time = self.calculate_travel_time("Sunset District", self.constraints[person]["location"])
                    meeting_time = self.schedule_meeting(person, current_time + travel_time, i - travel_time, self.constraints[person]["location"])
                    if meeting_time > 0:
                        current_time = i
        return self.itinerary

    def print_schedule(self):
        print("SOLUTION:")
        print(json.dumps({"itinerary": self.compute_optimal_schedule()}, indent=4))


if __name__ == "__main__":
    planner = MeetingPlanner()
    planner.print_schedule()