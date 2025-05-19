import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Berlin': 5,
            'Split': 3,
            'Bucharest': 3,
            'Riga': 5,
            'Lisbon': 3,
            'Tallinn': 4,
            'Lyon': 5
        }
        self.flights = {
            ('Lisbon', 'Bucharest'): 1,
            ('Berlin', 'Lisbon'): 1,
            ('Bucharest', 'Riga'): 1,
            ('Berlin', 'Riga'): 1,
            ('Split', 'Lyon'): 1,
            ('Lisbon', 'Riga'): 1,
            ('Riga', 'Tallinn'): 1,
            ('Berlin', 'Split'): 1,
            ('Lyon', 'Lisbon'): 1,
            ('Berlin', 'Tallinn'): 1,
            ('Lyon', 'Bucharest'): 1
        }
        self.conference = {'Berlin': (1, 5)}
        self.wedding = {'Lyon': (7, 11)}
        self.visiting_relatives = {'Bucharest': (13, 15)}

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
            elif city in self.visiting_relatives:
                start_day, end_day = self.visiting_relatives[city]
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