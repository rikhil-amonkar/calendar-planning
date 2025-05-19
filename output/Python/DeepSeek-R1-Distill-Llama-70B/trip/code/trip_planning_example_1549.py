import json
from datetime import datetime, timedelta

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Prague': 5,
            'Tallinn': 3,
            'Warsaw': 2,
            'Porto': 3,
            'Naples': 5,
            'Milan': 3,
            'Lisbon': 5,
            'Santorini': 5,
            'Riga': 4,
            'Stockholm': 2
        }
        self.events = {
            'Riga': (5, 8),
            'Tallinn': (18, 20),
            'Milan': (24, 26)
        }
        self.flights = {
            'Riga': ['Prague', 'Milan', 'Warsaw', 'Stockholm', 'Lisbon'],
            'Stockholm': ['Milan', 'Lisbon', 'Warsaw', 'Tallinn', 'Riga', 'Prague'],
            'Prague': ['Riga', 'Milan', 'Warsaw', 'Tallinn', 'Stockholm', 'Lisbon'],
            'Warsaw': ['Naples', 'Lisbon', 'Porto', 'Milan', 'Riga', 'Tallinn', 'Prague'],
            'Porto': ['Lisbon', 'Warsaw', 'Milan', 'Prague'],
            'Naples': ['Warsaw', 'Milan', 'Lisbon', 'Santorini'],
            'Milan': ['Porto', 'Naples', 'Lisbon', 'Santorini', 'Stockholm', 'Riga', 'Prague', 'Warsaw'],
            'Lisbon': ['Stockholm', 'Warsaw', 'Porto', 'Naples', 'Santorini', 'Riga', 'Prague', 'Milan'],
            'Santorini': ['Milan', 'Naples', 'Lisbon'],
            'Tallinn': ['Prague', 'Warsaw', 'Stockholm', 'Riga']
        }
        self.schedule = []
        self.current_day = 1

    def plan_trip(self):
        # Schedule fixed events first
        self.schedule_ri ga()
        self.schedule_tallinn()
        self.schedule_milan()
        
        # Schedule remaining cities
        self.schedule_stockholm()
        self.schedule_warsaw()
        self.schedule_porto()
        self.schedule_naples()
        self.schedule_lisbon()
        self.schedule_santorini()
        self.schedule_prague()
        
        return self.format_schedule()

    def schedule_ri ga(self):
        start_day = 5
        end_day = start_day + self.cities['Riga'] - 1
        if end_day > 8:
            end_day = 8
        self.add_place('Riga', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_tallinn(self):
        start_day = 18
        end_day = start_day + self.cities['Tallinn'] - 1
        if end_day > 20:
            end_day = 20
        self.add_place('Tallinn', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_milan(self):
        start_day = 24
        end_day = start_day + self.cities['Milan'] - 1
        if end_day > 26:
            end_day = 26
        self.add_place('Milan', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_stockholm(self):
        if self.current_day > 28:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Stockholm'] - 1
        if end_day > 28:
            end_day = 28
        self.add_place('Stockholm', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_warsaw(self):
        if self.current_day > 28:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Warsaw'] - 1
        if end_day > 28:
            end_day = 28
        self.add_place('Warsaw', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_porto(self):
        if self.current_day > 28:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Porto'] - 1
        if end_day > 28:
            end_day = 28
        self.add_place('Porto', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_naples(self):
        if self.current_day > 28:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Naples'] - 1
        if end_day > 28:
            end_day = 28
        self.add_place('Naples', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_lisbon(self):
        if self.current_day > 28:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Lisbon'] - 1
        if end_day > 28:
            end_day = 28
        self.add_place('Lisbon', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_santorini(self):
        if self.current_day > 28:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Santorini'] - 1
        if end_day > 28:
            end_day = 28
        self.add_place('Santorini', start_day, end_day)
        self.current_day = end_day + 1

    def schedule_prague(self):
        if self.current_day > 28:
            return
        start_day = self.current_day
        end_day = start_day + self.cities['Prague'] - 1
        if end_day > 28:
            end_day = 28
        self.add_place('Prague', start_day, end_day)
        self.current_day = end_day + 1

    def add_place(self, place, start_day, end_day):
        if start_day > 28 or end_day > 28:
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