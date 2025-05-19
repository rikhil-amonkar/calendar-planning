import json
from datetime import datetime, timedelta

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Split': 2,
            'Helsinki': 2,
            'Reykjavik': 3,
            'Vilnius': 3,
            'Geneva': 6
        }
        self.events = {
            'Reykjavik': (10, 12),
            'Vilnius': (7, 9)
        }
        self.flights = {
            'Split': ['Helsinki', 'Geneva', 'Vilnius'],
            'Helsinki': ['Split', 'Geneva', 'Reykjavik', 'Vilnius'],
            'Geneva': ['Split', 'Helsinki'],
            'Reykjavik': ['Helsinki'],
            'Vilnius': ['Helsinki']
        }
        self.schedule = []
        self.current_day = 1

    def plan_trip(self):
        # Schedule fixed events first
        self.schedule_reykjavik()
        self.schedule_vilnius()
        
        # Fill remaining days
        self.schedule_geneva()
        self.schedule_helsinki()
        self.schedule_split()
        
        return self.format_schedule()

    def schedule_reykjavik(self):
        start_day = 10
        end_day = start_day + self.cities['Reykjavik'] - 1
        if end_day > 12:
            end_day = 12
        self.add_place('Reykjavik', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_vilnius(self):
        start_day = 7
        end_day = start_day + self.cities['Vilnius'] - 1
        if end_day > 9:
            end_day = 9
        self.add_place('Vilnius', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_geneva(self):
        if self.current_day > 12:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Geneva'] - 1
        if end_day > 12:
            end_day = 12
        self.add_place('Geneva', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_helsinki(self):
        if self.current_day > 12:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Helsinki'] - 1
        if end_day > 12:
            end_day = 12
        self.add_place('Helsinki', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_split(self):
        if self.current_day > 12:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Split'] - 1
        if end_day > 12:
            end_day = 12
        self.add_place('Split', start_day, end_day)
        self.current_day = end_day + 1

    def add_place(self, place, start_day, end_day):
        if start_day > 12 or end_day > 12:
            return
        self.schedule.append({
            'day_range': f'Day {start_day}-{end_day}',
            'place': place
        })

    def add_flight(self, from_city, to_city, day):
        self.schedule.append({
            'flying': f'Day {day}-{day}',
            'from': from_city,
            'to': to_city
        })

    def format_schedule(self):
        # Add flights between places
        for i in range(1, len(self.schedule)):
            prev = self.schedule[i-1]
            current = self.schedule[i]
            if prev['place'] != current['place']:
                # Assume flight happens on the last day of previous place
                flight_day = prev['day_range'].split('-')[1].split()[1]
                self.add_flight(prev['place'], current['place'], flight_day)
        return self.schedule

def main():
    planner = TripPlanner()
    trip = planner.plan_trip()
    print(json.dumps(trip, indent=2))

if __name__ == "__main__":
    main()