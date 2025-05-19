import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Amsterdam': 4,
            'Edinburgh': 5,
            'Brussels': 5,
            'Vienna': 5,
            'Berlin': 4,
            'Reykjavik': 5
        }
        self.flights = {
            ('Edinburgh', 'Berlin'): 1,
            ('Amsterdam', 'Berlin'): 1,
            ('Edinburgh', 'Amsterdam'): 1,
            ('Vienna', 'Berlin'): 1,
            ('Berlin', 'Brussels'): 1,
            ('Vienna', 'Reykjavik'): 1,
            ('Edinburgh', 'Brussels'): 1,
            ('Vienna', 'Brussels'): 1,
            ('Amsterdam', 'Reykjavik'): 1,
            ('Reykjavik', 'Brussels'): 1,
            ('Amsterdam', 'Vienna'): 1,
            ('Reykjavik', 'Berlin'): 1
        }
        self.conference = {'Reykjavik': (12, 16)}
        self.meeting = {'Berlin': (16, 19)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.conference:
                start_day, end_day = self.conference[city]
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