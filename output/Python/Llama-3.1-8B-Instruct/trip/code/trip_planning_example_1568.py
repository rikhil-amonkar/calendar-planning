import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Prague': 5,
            'Brussels': 2,
            'Riga': 2,
            'Munich': 2,
            'Seville': 3,
            'Stockholm': 2,
            'Istanbul': 2,
            'Amsterdam': 3,
            'Vienna': 5,
            'Split': 3
        }
        self.flights = {
            ('Riga', 'Stockholm'): 1,
            ('Stockholm', 'Brussels'): 1,
            ('Istanbul', 'Munich'): 1,
            ('Istanbul', 'Riga'): 1,
            ('Prague', 'Split'): 1,
            ('Vienna', 'Brussels'): 1,
            ('Vienna', 'Riga'): 1,
            ('Split', 'Stockholm'): 1,
            ('Munich', 'Amsterdam'): 1,
            ('Split', 'Amsterdam'): 1,
            ('Amsterdam', 'Stockholm'): 1,
            ('Amsterdam', 'Riga'): 1,
            ('Vienna', 'Stockholm'): 1,
            ('Vienna', 'Istanbul'): 1,
            ('Vienna', 'Seville'): 1,
            ('Istanbul', 'Amsterdam'): 1,
            ('Munich', 'Brussels'): 1,
            ('Prague', 'Munich'): 1,
            ('Riga', 'Munich'): 1,
            ('Prague', 'Amsterdam'): 1,
            ('Prague', 'Brussels'): 1,
            ('Prague', 'Istanbul'): 1,
            ('Istanbul', 'Stockholm'): 1,
            ('Vienna', 'Prague'): 1,
            ('Munich', 'Split'): 1,
            ('Vienna', 'Amsterdam'): 1,
            ('Prague', 'Stockholm'): 1,
            ('Brussels', 'Seville'): 1,
            ('Munich', 'Stockholm'): 1,
            ('Istanbul', 'Brussels'): 1,
            ('Amsterdam', 'Seville'): 1,
            ('Vienna', 'Split'): 1,
            ('Munich', 'Seville'): 1,
            ('Riga', 'Brussels'): 1,
            ('Prague', 'Riga'): 1,
            ('Vienna', 'Munich'): 1
        }
        self.conference = {'Stockholm': (16, 17)}
        self.wedding = {'Vienna': (1, 5)}
        self.meeting = {'Riga': (15, 16)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.conference:
                start_day, end_day = self.conference[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.wedding:
                start_day, end_day = self.wedding[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.meeting:
                start_day, end_day = self.meeting[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            else:
                if current_city is not None:
                    for flight, duration in self.flights.items():
                        if flight[0] == current_city:
                            trip.append({'flying': f'Day {days}-{days}', 'from': current_city, 'to': flight[1]})
                            days += 1
                trip.append({'day_range': f'Day {days}-{days + duration - 1}', 'place': city})
                days += duration
                current_city = city
        if current_city is not None:
            for flight, duration in self.flights.items():
                if flight[0] == current_city:
                    trip.append({'flying': f'Day {days}-{days}', 'from': current_city, 'to': flight[1]})
                    days += 1
        return trip

    def output_json(self, trip):
        return json.dumps(trip, indent=4)

def main():
    planner = TripPlanner()
    trip = planner.plan_trip()
    print(planner.output_json(trip))

if __name__ == "__main__":
    main()