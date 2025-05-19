import json
from datetime import datetime, timedelta
from collections import defaultdict

class MeetingScheduler:
    def __init__(self):
        self.travel_times = {
            ('Marina District', 'Embarcadero'): 14,
            ('Marina District', 'Bayview'): 27,
            ('Marina District', 'Union Square'): 16,
            ('Marina District', 'Chinatown'): 15,
            ('Marina District', 'Sunset District'): 19,
            ('Marina District', 'Golden Gate Park'): 18,
            ('Marina District', 'Financial District'): 17,
            ('Marina District', 'Haight-Ashbury'): 16,
            ('Marina District', 'Mission District'): 20,
            ('Embarcadero', 'Marina District'): 12,
            ('Embarcadero', 'Bayview'): 21,
            ('Embarcadero', 'Union Square'): 10,
            ('Embarcadero', 'Chinatown'): 7,
            ('Embarcadero', 'Sunset District'): 30,
            ('Embarcadero', 'Golden Gate Park'): 25,
            ('Embarcadero', 'Financial District'): 5,
            ('Embarcadero', 'Haight-Ashbury'): 21,
            ('Embarcadero', 'Mission District'): 20,
            ('Bayview', 'Marina District'): 27,
            ('Bayview', 'Embarcadero'): 19,
            ('Bayview', 'Union Square'): 18,
            ('Bayview', 'Chinatown'): 19,
            ('Bayview', 'Sunset District'): 23,
            ('Bayview', 'Golden Gate Park'): 22,
            ('Bayview', 'Financial District'): 19,
            ('Bayview', 'Haight-Ashbury'): 19,
            ('Bayview', 'Mission District'): 13,
            ('Union Square', 'Marina District'): 18,
            ('Union Square', 'Embarcadero'): 11,
            ('Union Square', 'Bayview'): 15,
            ('Union Square', 'Chinatown'): 7,
            ('Union Square', 'Sunset District'): 27,
            ('Union Square', 'Golden Gate Park'): 22,
            ('Union Square', 'Financial District'): 9,
            ('Union Square', 'Haight-Ashbury'): 18,
            ('Union Square', 'Mission District'): 14,
            ('Chinatown', 'Marina District'): 12,
            ('Chinatown', 'Embarcadero'): 5,
            ('Chinatown', 'Bayview'): 20,
            ('Chinatown', 'Union Square'): 7,
            ('Chinatown', 'Sunset District'): 29,
            ('Chinatown', 'Golden Gate Park'): 23,
            ('Chinatown', 'Financial District'): 5,
            ('Chinatown', 'Haight-Ashbury'): 19,
            ('Chinatown', 'Mission District'): 17,
            ('Sunset District', 'Marina District'): 21,
            ('Sunset District', 'Embarcadero'): 30,
            ('Sunset District', 'Bayview'): 22,
            ('Sunset District', 'Union Square'): 30,
            ('Sunset District', 'Chinatown'): 30,
            ('Sunset District', 'Golden Gate Park'): 11,
            ('Sunset District', 'Financial District'): 30,
            ('Sunset District', 'Haight-Ashbury'): 15,
            ('Sunset District', 'Mission District'): 25,
            ('Golden Gate Park', 'Marina District'): 16,
            ('Golden Gate Park', 'Embarcadero'): 25,
            ('Golden Gate Park', 'Bayview'): 23,
            ('Golden Gate Park', 'Union Square'): 22,
            ('Golden Gate Park', 'Chinatown'): 23,
            ('Golden Gate Park', 'Sunset District'): 10,
            ('Golden Gate Park', 'Financial District'): 26,
            ('Golden Gate Park', 'Haight-Ashbury'): 7,
            ('Golden Gate Park', 'Mission District'): 17,
            ('Financial District', 'Marina District'): 15,
            ('Financial District', 'Embarcadero'): 4,
            ('Financial District', 'Bayview'): 19,
            ('Financial District', 'Union Square'): 9,
            ('Financial District', 'Chinatown'): 5,
            ('Financial District', 'Sunset District'): 30,
            ('Financial District', 'Golden Gate Park'): 23,
            ('Financial District', 'Haight-Ashbury'): 19,
            ('Financial District', 'Mission District'): 17,
            ('Haight-Ashbury', 'Marina District'): 17,
            ('Haight-Ashbury', 'Embarcadero'): 20,
            ('Haight-Ashbury', 'Bayview'): 18,
            ('Haight-Ashbury', 'Union Square'): 19,
            ('Haight-Ashbury', 'Chinatown'): 19,
            ('Haight-Ashbury', 'Sunset District'): 15,
            ('Haight-Ashbury', 'Golden Gate Park'): 7,
            ('Haight-Ashbury', 'Financial District'): 21,
            ('Haight-Ashbury', 'Mission District'): 11,
            ('Mission District', 'Marina District'): 19,
            ('Mission District', 'Embarcadero'): 19,
            ('Mission District', 'Bayview'): 14,
            ('Mission District', 'Union Square'): 15,
            ('Mission District', 'Chinatown'): 16,
            ('Mission District', 'Sunset District'): 24,
            ('Mission District', 'Golden Gate Park'): 17,
            ('Mission District', 'Financial District'): 15,
            ('Mission District', 'Haight-Ashbury'): 12,
        }

        self.meeting_requirements = {
            "Joshua": {"location": "Embarcadero", "min_time": 105, "available": [datetime(2023,1,1,9,45), datetime(2023,1,1,18,0)]},
            "Jeffrey": {"location": "Bayview", "min_time": 75, "available": [datetime(2023,1,1,9,45), datetime(2023,1,1,20,15)]},
            "Charles": {"location": "Union Square", "min_time": 120, "available": [datetime(2023,1,1,10,45), datetime(2023,1,1,20,15)]},
            "Joseph": {"location": "Chinatown", "min_time": 60, "available": [datetime(2023,1,1,7,0), datetime(2023,1,1,15,30)]},
            "Elizabeth": {"location": "Sunset District", "min_time": 45, "available": [datetime(2023,1,1,9,0), datetime(2023,1,1,9,45)]},
            "Matthew": {"location": "Golden Gate Park", "min_time": 45, "available": [datetime(2023,1,1,11,0), datetime(2023,1,1,19,30)]},
            "Carol": {"location": "Financial District", "min_time": 15, "available": [datetime(2023,1,1,10,45), datetime(2023,1,1,11,15)]},
            "Paul": {"location": "Haight-Ashbury", "min_time": 15, "available": [datetime(2023,1,1,19,15), datetime(2023,1,1,20,30)]},
            "Rebecca": {"location": "Mission District", "min_time": 45, "available": [datetime(2023,1,1,17,0), datetime(2023,1,1,21,15)]},
        }
        
        self.init_times()

    def init_times(self):
        self.start_time = datetime(2023, 1, 1, 9, 0)
        self.itinerary = []
    
    def add_meeting(self, person, start, duration):
        location = self.meeting_requirements[person]["location"]
        end = start + timedelta(minutes=duration)
        self.itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start.strftime("%H:%M"),
            "end_time": end.strftime("%H:%M"),
        })
    
    def can_meet(self, person, start, duration):
        end = start + timedelta(minutes=duration)
        available_start, available_end = self.meeting_requirements[person]["available"]
        return (available_start <= start <= available_end) and (available_start <= end <= available_end)

    def schedule_meetings(self):
        current_time = self.start_time
        locations_visited = set()
        
        # Meet Elizabeth first because time is limited
        if self.can_meet("Elizabeth", current_time, 45):
            self.add_meeting("Elizabeth", current_time, 45)
            current_time += timedelta(minutes=45)

        # Meet Joseph
        if self.can_meet("Joseph", current_time, 60):
            self.add_meeting("Joseph", current_time, 60)
            current_time += timedelta(minutes=60)

        # Meet Joshua
        if self.can_meet("Joshua", current_time, 105):
            self.add_meeting("Joshua", current_time, 105)
            current_time += timedelta(minutes=105)

        # Meet Carol
        if self.can_meet("Carol", current_time, 15):
            self.add_meeting("Carol", current_time, 15)
            current_time += timedelta(minutes=15)

        # Meet Charles
        if self.can_meet("Charles", current_time, 120):
            self.add_meeting("Charles", current_time, 120)
            current_time += timedelta(minutes=120)

        # Meet Matthew
        if self.can_meet("Matthew", current_time, 45):
            self.add_meeting("Matthew", current_time, 45)
            current_time += timedelta(minutes=45)

        # Meet Rebecca
        if self.can_meet("Rebecca", current_time, 45):
            self.add_meeting("Rebecca", current_time, 45)
            current_time += timedelta(minutes=45)

        # Meet Paul
        if self.can_meet("Paul", current_time, 15):
            self.add_meeting("Paul", current_time, 15)

        # Print output in the required JSON format
        print(json.dumps({"itinerary": self.itinerary}, indent=2))

if __name__ == '__main__':
    scheduler = MeetingScheduler()
    scheduler.schedule_meetings()