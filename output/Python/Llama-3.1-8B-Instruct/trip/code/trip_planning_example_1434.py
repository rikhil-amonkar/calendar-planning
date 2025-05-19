import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Rome': 3,
            'Mykonos': 2,
            'Lisbon': 2,
            'Frankfurt': 5,
            'Nice': 3,
            'Stuttgart': 4,
            'Venice': 4,
            'Dublin': 2,
            'Bucharest': 2,
            'Seville': 5
        }
        self.flights = {
            ('Rome', 'Stuttgart'): 1,
            ('Venice', 'Rome'): 1,
            ('Dublin', 'Bucharest'): 1,
            ('Mykonos', 'Rome'): 1,
            ('Seville', 'Lisbon'): 1,
            ('Frankfurt', 'Venice'): 1,
            ('Venice', 'Stuttgart'): 1,
            ('Bucharest', 'Lisbon'): 1,
            ('Nice', 'Mykonos'): 1,
            ('Venice', 'Lisbon'): 1,
            ('Dublin', 'Lisbon'): 1,
            ('Venice', 'Nice'): 1,
            ('Rome', 'Seville'): 1,
            ('Frankfurt', 'Rome'): 1,
            ('Nice', 'Dublin'): 1,
            ('Rome', 'Bucharest'): 1,
            ('Frankfurt', 'Dublin'): 1,
            ('Rome', 'Dublin'): 1,
            ('Venice', 'Dublin'): 1,
            ('Rome', 'Lisbon'): 1,
            ('Frankfurt', 'Lisbon'): 1,
            ('Nice', 'Rome'): 1,
            ('Frankfurt', 'Nice'): 1,
            ('Frankfurt', 'Stuttgart'): 1,
            ('Frankfurt', 'Bucharest'): 1,
            ('Lisbon', 'Stuttgart'): 1,
            ('Nice', 'Lisbon'): 1,
            ('Seville', 'Dublin'): 1
        }
        self.conference = {'Seville': (13, 17)}
        self.wedding = {'Frankfurt': (1, 5)}

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