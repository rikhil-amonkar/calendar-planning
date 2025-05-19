import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Venice': 3,
            'Reykjavik': 2,
            'Munich': 3,
            'Santorini': 3,
            'Manchester': 3,
            'Porto': 3,
            'Bucharest': 5,
            'Tallinn': 4,
            'Valencia': 2,
            'Vienna': 5
        }
        self.flights = {
            ('Bucharest', 'Manchester'): 1,
            ('Munich', 'Venice'): 1,
            ('Santorini', 'Manchester'): 1,
            ('Vienna', 'Reykjavik'): 1,
            ('Venice', 'Santorini'): 1,
            ('Munich', 'Porto'): 1,
            ('Valencia', 'Vienna'): 1,
            ('Manchester', 'Vienna'): 1,
            ('Porto', 'Vienna'): 1,
            ('Venice', 'Manchester'): 1,
            ('Santorini', 'Vienna'): 1,
            ('Munich', 'Manchester'): 1,
            ('Munich', 'Reykjavik'): 1,
            ('Bucharest', 'Valencia'): 1,
            ('Venice', 'Vienna'): 1,
            ('Bucharest', 'Vienna'): 1,
            ('Porto', 'Manchester'): 1,
            ('Munich', 'Vienna'): 1,
            ('Valencia', 'Porto'): 1,
            ('Munich', 'Bucharest'): 1,
            ('Tallinn', 'Munich'): 1,
            ('Santorini', 'Bucharest'): 1,
            ('Munich', 'Valencia'): 1
        }
        self.conference = {'Munich': (4, 6)}
        self.wedding = {'Santorini': (8, 10)}
        self.workshop = {'Valencia': (14, 15)}

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
            elif city in self.workshop:
                start_day, end_day = self.workshop[city]
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