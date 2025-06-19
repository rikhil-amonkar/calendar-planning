import json
from datetime import datetime, timedelta

class MeetingScheduler:
    def __init__(self):
        self.travel_times = {
            'Pacific Heights': {
                'Marina District': 6,
                'The Castro': 16,
                'Richmond District': 12,
                'Alamo Square': 10,
                'Financial District': 13,
                'Presidio': 11,
                'Mission District': 15,
                'Nob Hill': 8,
                'Russian Hill': 7
            },
            'Marina District': {
                'Pacific Heights': 7,
                'The Castro': 22,
                'Richmond District': 11,
                'Alamo Square': 15,
                'Financial District': 17,
                'Presidio': 10,
                'Mission District': 20,
                'Nob Hill': 12,
                'Russian Hill': 8
            },
            'The Castro': {
                'Pacific Heights': 16,
                'Marina District': 21,
                'Richmond District': 16,
                'Alamo Square': 8,
                'Financial District': 21,
                'Presidio': 20,
                'Mission District': 7,
                'Nob Hill': 16,
                'Russian Hill': 18
            },
            'Richmond District': {
                'Pacific Heights': 10,
                'Marina District': 9,
                'The Castro': 16,
                'Alamo Square': 13,
                'Financial District': 22,
                'Presidio': 7,
                'Mission District': 20,
                'Nob Hill': 17,
                'Russian Hill': 13
            },
            'Alamo Square': {
                'Pacific Heights': 10,
                'Marina District': 15,
                'The Castro': 8,
                'Richmond District': 11,
                'Financial District': 17,
                'Presidio': 17,
                'Mission District': 10,
                'Nob Hill': 11,
                'Russian Hill': 13
            },
            'Financial District': {
                'Pacific Heights': 13,
                'Marina District': 15,
                'The Castro': 20,
                'Richmond District': 21,
                'Alamo Square': 17,
                'Presidio': 22,
                'Mission District': 17,
                'Nob Hill': 8,
                'Russian Hill': 11
            },
            'Presidio': {
                'Pacific Heights': 11,
                'Marina District': 11,
                'The Castro': 21,
                'Richmond District': 7,
                'Alamo Square': 19,
                'Financial District': 23,
                'Mission District': 26,
                'Nob Hill': 18,
                'Russian Hill': 14
            },
            'Mission District': {
                'Pacific Heights': 16,
                'Marina District': 19,
                'The Castro': 7,
                'Richmond District': 20,
                'Alamo Square': 11,
                'Financial District': 15,
                'Presidio': 25,
                'Nob Hill': 12,
                'Russian Hill': 15
            },
            'Nob Hill': {
                'Pacific Heights': 8,
                'Marina District': 11,
                'The Castro': 17,
                'Richmond District': 14,
                'Alamo Square': 11,
                'Financial District': 9,
                'Presidio': 17,
                'Mission District': 13,
                'Russian Hill': 5
            },
            'Russian Hill': {
                'Pacific Heights': 7,
                'Marina District': 7,
                'The Castro': 21,
                'Richmond District': 14,
                'Alamo Square': 15,
                'Financial District': 11,
                'Presidio': 14,
                'Mission District': 16,
                'Nob Hill': 5
            }
        }
        self.constraints = {
            'Linda': {'start_time': 18, 'end_time': 22,'min_time': 30, 'location': 'Financial District'},
            'Kenneth': {'start_time': 14, 'end_time': 16,'min_time': 30},
            'Kimberly': {'start_time': 14, 'end_time': 22,'min_time': 30},
            'Paul': {'start_time': 21, 'end_time': 21,'min_time': 15},
            'Carol': {'start_time': 10, 'end_time': 12,'min_time': 60},
            'Brian': {'start_time': 10, 'end_time': 21,'min_time': 75},
            'Laura': {'start_time': 16, 'end_time': 20,'min_time': 30},
            'Sandra': {'start_time': 9, 'end_time': 18,'min_time': 60},
            'Karen': {'start_time': 18, 'end_time': 22,'min_time': 75}
        }
        self.itinerary = []

    def schedule_meeting(self, person, start_time, end_time, location):
        if start_time < 9 or end_time > 22:
            return
        if person in self.constraints:
            constraint = self.constraints[person]
            if 'location' in constraint:
                travel_time = self.travel_times[constraint['location']][location]
                start_time += travel_time
                end_time += travel_time
            else:
                # Assign a default location if it's not specified
                default_location = 'Pacific Heights'
                travel_time = self.travel_times[default_location][location]
                start_time += travel_time
                end_time += travel_time
            self.itinerary.append({'action':'meet', 'location': location, 'person': person,'start_time': f"{start_time // 60:02d}:{start_time % 60:02d}", 'end_time': f"{end_time // 60:02d}:{end_time % 60:02d}"})
            return
        return

    def optimize_schedule(self):
        start_time = 9
        while start_time <= 22:
            for person, constraint in self.constraints.items():
                if 'location' in constraint:
                    if start_time >= constraint['start_time'] and start_time + constraint['min_time'] <= constraint['end_time']:
                        location = constraint['location']
                        travel_time = self.travel_times[location]['Pacific Heights']
                        self.schedule_meeting(person, start_time, start_time + constraint['min_time'], location)
                else:
                    for i in range(75, 0, -15):
                        if start_time + i <= 22:
                            self.schedule_meeting(person, start_time, start_time + i, 'Pacific Heights')
            start_time += 30

    def generate_itinerary(self):
        self.optimize_schedule()
        return json.dumps(self.itinerary, indent=4)

if __name__ == "__main__":
    scheduler = MeetingScheduler()
    print(scheduler.generate_itinerary())