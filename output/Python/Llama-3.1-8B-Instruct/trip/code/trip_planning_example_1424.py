import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Warsaw': 3,
            'Porto': 5,
            'Naples': 4,
            'Brussels': 3,
            'Split': 3,
            'Reykjavik': 5,
            'Amsterdam': 4,
            'Lyon': 3,
            'Helsinki': 4,
            'Valencia': 2
        }
        self.flights = {
            ('Amsterdam', 'Warsaw'): 1,
            ('Helsinki', 'Brussels'): 1,
            ('Helsinki', 'Warsaw'): 1,
            ('Reykjavik', 'Brussels'): 1,
            ('Amsterdam', 'Lyon'): 1,
            ('Amsterdam', 'Naples'): 1,
            ('Amsterdam', 'Reykjavik'): 1,
            ('Naples', 'Valencia'): 1,
            ('Porto', 'Brussels'): 1,
            ('Amsterdam', 'Split'): 1,
            ('Lyon', 'Split'): 1,
            ('Warsaw', 'Split'): 1,
            ('Porto', 'Amsterdam'): 1,
            ('Helsinki', 'Split'): 1,
            ('Brussels', 'Lyon'): 1,
            ('Porto', 'Lyon'): 1,
            ('Reykjavik', 'Warsaw'): 1,
            ('Brussels', 'Valencia'): 1,
            ('Valencia', 'Lyon'): 1,
            ('Porto', 'Warsaw'): 1,
            ('Warsaw', 'Valencia'): 1,
            ('Amsterdam', 'Helsinki'): 1,
            ('Porto', 'Valencia'): 1,
            ('Warsaw', 'Brussels'): 1,
            ('Warsaw', 'Naples'): 1,
            ('Naples', 'Split'): 1,
            ('Helsinki', 'Naples'): 1,
            ('Helsinki', 'Reykjavik'): 1,
            ('Amsterdam', 'Valencia'): 1,
            ('Naples', 'Brussels'): 1
        }
        self.conference = {'Naples': (17, 20)}
        self.workshop = {'Porto': (1, 5)}
        self.meeting = {'Amsterdam': (5, 8)}
        self.wedding = {'Helsinki': (8, 11)}

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
            elif city in self.wedding:
                start_day, end_day = self.wedding[city]
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