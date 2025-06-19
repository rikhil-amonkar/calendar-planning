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
        # Sort people by their start time
        sorted_people = sorted(self.constraints.items(), key=lambda x: x[1]["start_time"])

        # Initialize the current time and location
        current_time = self.arrival_time * 100
        current_location = "Sunset District"

        for person, constraints in sorted_people:
            travel_time = self.calculate_travel_time(current_location, constraints["location"])
            current_time += travel_time
            current_location = constraints["location"]

            # Check if the person is available at the current time
            for i in range(constraints["start_time"] * 100, constraints["end_time"] * 100):
                if i >= current_time:
                    meeting_time = self.schedule_meeting(person, current_time, i, constraints["location"])
                    if meeting_time > 0:
                        current_time = i
                        break

        # Ensure all people have been scheduled
        for person in self.constraints:
            if person not in [item["person"] for item in self.itinerary]:
                self.itinerary.append({
                    "action": "unavailable",
                    "person": person,
                    "start_time": f"{self.arrival_time // 100}:{self.arrival_time % 100:02}",
                    "end_time": f"{self.arrival_time // 100}:{self.arrival_time % 100:02}"
                })

        return self.itinerary

    def print_schedule(self):
        print("SOLUTION:")
        print(json.dumps({"itinerary": self.compute_optimal_schedule()}, indent=4))


if __name__ == "__main__":
    planner = MeetingPlanner()
    planner.print_schedule()