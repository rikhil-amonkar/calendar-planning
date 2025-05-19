import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Dublin': 3,
            'Madrid': 2,
            'Oslo': 3,
            'London': 2,
            'Vilnius': 3,
            'Berlin': 5
        }
        self.flights = {
            ('London', 'Madrid'): 1,
            ('Oslo', 'Vilnius'): 1,
            ('Berlin', 'Vilnius'): 1,
            ('Madrid', 'Oslo'): 1,
            ('Madrid', 'Dublin'): 1,
            ('London', 'Oslo'): 1,
            ('Madrid', 'Berlin'): 1,
            ('Berlin', 'Oslo'): 1,
            ('Dublin', 'Oslo'): 1,
            ('London', 'Dublin'): 1,
            ('London', 'Berlin'): 1,
            ('Berlin', 'Dublin'): 1
        }
        self.conference = {'Dublin': (7, 9)}
        self.wedding = {'Berlin': (3, 7)}
        self.meeting = {'Dublin': (7, 9)}

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