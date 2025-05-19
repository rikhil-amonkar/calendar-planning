import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Oslo': 2,
            'Reykjavik': 5,
            'Stockholm': 4,
            'Munich': 4,
            'Frankfurt': 4,
            'Barcelona': 3,
            'Bucharest': 2,
            'Split': 3
        }
        self.flights = {
            ('Reykjavik', 'Munich'): 1,
            ('Munich', 'Frankfurt'): 1,
            ('Split', 'Oslo'): 1,
            ('Reykjavik', 'Oslo'): 1,
            ('Bucharest', 'Munich'): 1,
            ('Oslo', 'Frankfurt'): 1,
            ('Bucharest', 'Barcelona'): 1,
            ('Barcelona', 'Frankfurt'): 1,
            ('Reykjavik', 'Frankfurt'): 1,
            ('Barcelona', 'Stockholm'): 1,
            ('Barcelona', 'Reykjavik'): 1,
            ('Stockholm', 'Reykjavik'): 1,
            ('Barcelona', 'Split'): 1,
            ('Bucharest', 'Oslo'): 1,
            ('Bucharest', 'Frankfurt'): 1,
            ('Split', 'Stockholm'): 1,
            ('Barcelona', 'Oslo'): 1,
            ('Stockholm', 'Munich'): 1,
            ('Stockholm', 'Oslo'): 1,
            ('Split', 'Frankfurt'): 1,
            ('Barcelona', 'Munich'): 1,
            ('Stockholm', 'Frankfurt'): 1,
            ('Munich', 'Oslo'): 1,
            ('Split', 'Munich'): 1
        }
        self.conference = {'Oslo': (16, 17)}
        self.workshop = {'Frankfurt': (17, 20)}
        self.meeting = {'Reykjavik': (9, 13)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.conference:
                start_day, end_day = self.conference[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.workshop:
                start_day, end_day = self.workshop[city]
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