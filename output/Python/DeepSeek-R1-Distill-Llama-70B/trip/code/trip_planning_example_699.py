import json
from datetime import datetime, timedelta

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Mykonos': 3,
            'Reykjavik': 2,
            'Dublin': 5,
            'London': 5,
            'Helsinki': 4,
            'Hamburg': 2
        }
        self.events = {
            'Reykjavik': (9, 10),
            'Dublin': (2, 6),
            'Hamburg': (1, 2)
        }
        self.flights = {
            'Dublin': ['London', 'Hamburg', 'Helsinki', 'Reykjavik'],
            'Hamburg': ['Dublin', 'London', 'Helsinki'],
            'Helsinki': ['Reykjavik', 'London', 'Dublin', 'Hamburg'],
            'Reykjavik': ['London', 'Dublin', 'Helsinki'],
            'London': ['Dublin', 'Hamburg', 'Helsinki', 'Reykjavik', 'Mykonos'],
            'Mykonos': ['London']
        }
        self.schedule = []
        self.current_day = 1

    def plan_trip(self):
        # Schedule fixed events first
        self.schedule_hamburg()
        self.schedule_dublin()
        self.schedule_reykjavik()
        
        # Schedule remaining cities
        self.schedule_helsinki()
        self.schedule_london()
        self.schedule_mykonos()
        
        return self.format_schedule()

    def schedule_hamburg(self):
        start_day = 1
        end_day = start_day + self.cities['Hamburg'] - 1
        if end_day > 16:
            end_day = 16
        self.add_place('Hamburg', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_dublin(self):
        start_day = 2
        end_day = start_day + self.cities['Dublin'] - 1
        if end_day > 16:
            end_day = 16
        self.add_place('Dublin', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_reykjavik(self):
        start_day = 9
        end_day = start_day + self.cities['Reykjavik'] - 1
        if end_day > 16:
            end_day = 16
        self.add_place('Reykjavik', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_helsinki(self):
        if self.current_day > 16:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Helsinki'] - 1
        if end_day > 16:
            end_day = 16
        self.add_place('Helsinki', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_london(self):
        if self.current_day > 16:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['London'] - 1
        if end_day > 16:
            end_day = 16
        self.add_place('London', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_mykonos(self):
        if self.current_day > 16:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Mykonos'] - 1
        if end_day > 16:
            end_day = 16
        self.add_place('Mykonos', start_day, end_day)
        self.current_day = end_day + 1

    def add_place(self, place, start_day, end_day):
        if start_day > 16 or end_day > 16:
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